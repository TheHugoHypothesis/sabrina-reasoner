import Logic.FOL.Parser
import Logic.FOL.Printer

namespace Logic.CLI.Roundtrip


/-!
# Round-trip gate (Stage 1)

`lake exe bfo-roundtrip <file>…` reads CLIF axiom files, parses them, and checks three
things per axiom:

1. **structural faithfulness** — turning the parsed formula back into an S-expression
   reproduces the source S-expression, modulo the only normalization the AST performs
   (n-ary `and`/`or` left-associated);
2. **textual faithfulness** — the printed CLIF is the source text (up to whitespace),
   which is the closest executable form of `print (parse s) = s`;
3. **idempotence** — the printed CLIF re-parses to the same formula;
4. **closure** — every axiom is a sentence, i.e. has no free variables, which is the
   check that the parser's scope handling turned bound names into variables and
   unbound names into constants.

This is a runtime check over the real artifacts, so it is evidence about the parser
(the untrusted side) rather than a proof. Text differences are diagnostic; structural,
reparse, closure and file failures exit non-zero. Use bfo-audit for source coverage.
-/

open Logic.FOL

/-- Per-file outcome. -/
structure Report where
  file : String
  axioms : Nat
  sexpMismatch : Nat
  textMismatch : Nat
  printMismatch : Nat
  openFormulas : Nat
  errors : List String

/-- One axiom: source S-expression versus what the AST preserves. -/
def checkAxiom (a : Axiom) : Except String Bool := do
  let φ := a.formula
  -- 1. AST → S-expression must match the normalized source form
  if Formula.toSexp φ != normalizeSexp a.sexp then Except.error "sexp round trip differs"
  -- 2. AST → CLIF text → AST must be the identity
  let printed := φ.toClif (fun x => x) (fun r => r) (fun f => f)
  let sexps ← match sexpFromTokens (tokenize printed) with
    | some ss => pure ss
    | none => Except.error "printed CLIF does not re-tokenize"
  let φ' ← match sexps with
    | [s] => parseFormula [] s
    | _ => Except.error "printed CLIF is not one formula"
  if φ != φ' then Except.error "printed CLIF re-parses differently"
  pure φ.isSentence

/-- A report for a file that could not be tokenized/parsed at all. -/
def unparsable (path : String) : Report :=
  { file := path, axioms := 0, sexpMismatch := 0, textMismatch := 0, printMismatch := 0,
    openFormulas := 0, errors := ["unparsable file"] }

def checkFile (path : String) : IO Report := do
  let text ← IO.FS.readFile path
  let tokens ← match tokenizeChecked text with
    | .ok tokens => pure tokens
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      return { (unparsable path) with errors := [e] }
  match sexpFromTokens tokens with
  | none =>
      IO.eprintln s!"{path}: unterminated brackets or quotes"
      pure (unparsable path)
  | some sexps =>
      let axioms ← match collectAxioms sexps with
        | .ok axioms => pure axioms
        | .error e =>
          IO.eprintln s!"{path}: {e}"
          return { (unparsable path) with errors := [e] }
      let mut sexpMismatch := 0
      let mut textMismatch := 0
      let mut printMismatch := 0
      let mut openFormulas := 0
      let mut errors : List String := []
      for a in axioms do
        if Formula.toSexp a.formula != normalizeSexp a.sexp then
          sexpMismatch := sexpMismatch + 1
          errors := errors ++ [s!"[{a.tag}] sexp round trip differs"]
        -- whitespace-insensitive text comparison: printed CLIF versus the source form
        let printed := a.formula.toClif (fun x => x) (fun r => r) (fun f => f)
        if Token.join (tokenize printed) != Token.join (tokenize (Sexp.toText a.sexp)) then
          textMismatch := textMismatch + 1
          errors := errors ++ [s!"[{a.tag}] printed CLIF is not the source text"]
        match checkAxiom a with
        | .error e =>
            printMismatch := printMismatch + 1
            errors := errors ++ [s!"[{a.tag}] {e}"]
        | .ok isSent =>
            if !isSent then
              openFormulas := openFormulas + 1
              errors := errors ++ [s!"[{a.tag}] has free variables"]
      pure { file := path, axioms := axioms.length, sexpMismatch, textMismatch,
             printMismatch, openFormulas, errors }

def run (args : List String) : IO Unit := do
  if args.isEmpty then
    IO.eprintln "usage: bfo-roundtrip <file.cl>…"
    IO.Process.exit 1
  let mut total := 0
  let mut bad := 0
  IO.println "file | axioms | sexp≠ | text≠ | print≠ | open"
  for path in args do
    let r ← checkFile path
    total := total + r.axioms
    bad := bad + r.sexpMismatch + r.printMismatch + r.openFormulas + (if r.axioms == 0 then 1 else 0)
    IO.println s!"{path} | {r.axioms} | {r.sexpMismatch} | {r.textMismatch} | {r.printMismatch} | {r.openFormulas}"
    for e in r.errors.take 5 do IO.eprintln s!"   {e}"
  IO.println s!"total axioms parsed: {total}; blocking discrepancies: {bad} (text differences reported separately)"
  if bad > 0 then IO.Process.exit 1

end Logic.CLI.Roundtrip
