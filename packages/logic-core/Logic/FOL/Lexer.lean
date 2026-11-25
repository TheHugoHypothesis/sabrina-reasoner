/-!
# CLIF lexer

The upstream files are S-expressions with `cl:` wrapper forms, quoted strings for
comments and IRIs, and identifiers built from letters, digits, `-`, `_`, `.` and `:`.
Quoting matters: the license header contains parentheses and apostrophes, so a lexer
that ignores strings mis-reads the file header as formula syntax.

`tokenize` is a total char-by-char state machine (no `partial`, no well-founded
recursion), so it is kernel-reducible and the module stays axiom-free.
-/

namespace Logic.FOL

inductive Token where
  | openP  : Token
  | closeP : Token
  | ident  : String → Token
  | quoted : String → Token
  deriving BEq, Repr

def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_' || c == '.' || c == ':' || c == '='

def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- Lexer state: an open identifier run, an open quoted run, or an inline comment. -/
inductive Mode where
  | none
  | ident (buf : List Char)
  /-- `escaped` records a trailing backslash: CLIF labels use `\'` for an apostrophe
  inside a quoted comment, e.g. `doesn\'t` in `material-entity.cl`. -/
  | quote (q : Char) (escaped : Bool) (buf : List Char)
  | comment

structure LexState where
  toks : List Token      -- reversed
  mode : Mode

def flush (st : LexState) : LexState :=
  match st.mode with
  | .ident buf => { toks := Token.ident (String.ofList buf.reverse) :: st.toks, mode := .none }
  | .quote _ _ buf => { toks := Token.quoted (String.ofList buf.reverse) :: st.toks, mode := .none }
  | _ => st

/-- One character of the lexer. -/
def lexStep (st : LexState) (c : Char) : LexState :=
  match st.mode with
  | .comment => if c == '\n' then { toks := st.toks, mode := .none } else st
  | .quote q escaped buf =>
      if escaped then { toks := st.toks, mode := .quote q false (c :: buf) }
      else if c == '\\' then { toks := st.toks, mode := .quote q true (c :: buf) }
      else if c == q then { toks := Token.quoted (String.ofList (buf.reverse ++ [q])) :: st.toks, mode := .none }
      else { toks := st.toks, mode := .quote q false (c :: buf) }
  | .ident buf =>
      if isIdentChar c then { toks := st.toks, mode := .ident (c :: buf) }
      else
        let st' := flush { toks := st.toks, mode := .ident buf }
        lexPunct st' c
  | .none => lexPunct st c
where
  lexPunct (st : LexState) (c : Char) : LexState :=
    if isSpace c then { toks := st.toks, mode := .none }
    else if c == '(' then { toks := Token.openP :: st.toks, mode := .none }
    else if c == ')' then { toks := Token.closeP :: st.toks, mode := .none }
    else if c == ';' then { toks := st.toks, mode := .comment }
    else if c == '\'' || c == '"' then { toks := st.toks, mode := .quote c false [c] }
    else if isIdentChar c then { toks := st.toks, mode := .ident [c] }
    -- Unknown characters (non-ASCII, stray punctuation) are dropped, which the
    -- round-trip gate detects: the artifacts contain none of them.
    else { toks := st.toks, mode := .none }

/-- Tokenize CLIF text, in source order. -/
def tokenize (text : String) : List Token :=
  (flush (List.foldl (fun st c => lexStep st c) { toks := [], mode := .none } text.toList)).toks.reverse

/-- Reject unsupported characters and unterminated quotes instead of silently
normalizing them away. Intended for source import and auditing. -/
def tokenizeChecked (text : String) : Except String (List Token) := do
  let mut st : LexState := { toks := [], mode := .none }
  for c in text.toList do
    let valid := match st.mode with
      | .quote .. | .comment => true
      | _ => isSpace c || isIdentChar c || c == '(' || c == ')' ||
             c == ';' || c == '\'' || c == '"'
    if !valid then throw s!"unsupported character: {c}"
    st := lexStep st c
  match st.mode with
  | .quote .. => throw "unterminated quoted string"
  | _ => pure (flush st).toks.reverse

/-- Render tokens back with canonical single-space separation; used by the round-trip
gate, which compares token streams rather than whitespace. -/
def Token.join (ts : List Token) : String :=
  String.intercalate " " (ts.map fun t => match t with
    | .openP => "("
    | .closeP => ")"
    | .ident s => s
    | .quoted s => s)

end Logic.FOL
