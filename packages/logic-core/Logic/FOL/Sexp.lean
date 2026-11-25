import Logic.FOL.Lexer

/-!
# S-expressions

CLIF is S-expression syntax, and the axiom files wrap their formulas in `cl:` forms.
Keeping S-expressions as their own type lets the parser be checked against them: the
Stage 1 faithfulness gate is "turning a parsed formula back into an S-expression
recovers the source form", which is a statement about this intermediate representation,
not about pretty-printing.
-/

namespace Logic.FOL

inductive Sexp where
  | atom : String → Sexp
  | list : List Sexp → Sexp
  deriving BEq, Repr

instance : Coe Sexp String where coe := fun s => match s with
  | .atom t => t
  | .list _ => "(…)"

/-- Build a well-bracketed list of S-expressions from tokens. `none` means the token
list is not a closed sequence of S-expressions — a truncated artifact is reported as a
parse failure rather than silently losing the last form. -/
def sexpFromTokens (ts : List Token) : Option (List Sexp) :=
  go ts [] []
where
  go (ts : List Token) (stack : List (List Sexp)) (acc : List Sexp) : Option (List Sexp) :=
    match ts with
    | [] => if stack.isEmpty then some acc.reverse else none
    | Token.openP :: rest => go rest (acc :: stack) []
    | Token.closeP :: rest =>
        match stack with
        | [] => none
        | outer :: stack' => go rest stack' (Sexp.list acc.reverse :: outer)
    | Token.ident s :: rest => go rest stack (Sexp.atom s :: acc)
    | Token.quoted s :: rest => go rest stack (Sexp.atom (quoteText s) :: acc)
  quoteText (s : String) : String := s

/-- Canonical rendering, used for error messages and for the token-level round trip. -/
def Sexp.toText : Sexp → String
  | .atom s => s
  | .list xs => "(" ++ String.intercalate " " (xs.map Sexp.toText) ++ ")"

/-- Is this the head symbol of a list form? -/
def Sexp.head? : Sexp → Option String
  | .list (Sexp.atom s :: _) => some s
  | _ => none

/-- Children of a list form. -/
def Sexp.args : Sexp → List Sexp
  | .list xs => xs
  | .atom _ => []

/-- The text of an atom, if this is an atom. -/
def Sexp.atom? : Sexp → Option String
  | .atom s => some s
  | .list _ => none

end Logic.FOL
