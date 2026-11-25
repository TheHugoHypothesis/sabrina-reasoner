import Logic.FOL.Sexp
import Logic.FOL.Syntax

/-!
# CLIF parser

Parses the CLIF forms used by the BFO 2020 artifacts into `Term`/`Formula` over
`String` symbols:

* term position: an identifier in the scope of an enclosing quantifier is a variable,
  otherwise it is a nullary function symbol (a constant). This distinction cannot be
  made from the text alone, so the parser carries a scope; getting it wrong would make
  `instance-of a independent-continuant t` read the universal as a free variable.
* `and`/`or` are n-ary in CLIF (up to 6 arguments in these files) and become
  left-associated binary connectives here; this is the only structural normalization.
* quantifiers group their variables, matching CLIF and the printer.
* formulas are wrapped in `(cl:comment 'label [tag]' formula)`; the tag inside the
  label is what identifies an axiom, so `collectAxioms` walks the wrappers and returns
  `(tag, label, formula)` triples.

`ofSexp`/`toSexp` are the two directions used by the round-trip gate in `Main.lean`.
-/

namespace Logic.FOL

/-- The bracketed tag in a comment label, e.g. `mcd-1`, taken from the label of a
`cl:comment` wrapper: scan the character list for `[` … `]`. -/
def extractTag (text : String) : Option String :=
  go text.toList false []
where
  go (cs : List Char) (openBracket : Bool) (acc : List Char) : Option String :=
    match cs with
    | [] => none
    | '[' :: _rest => go _rest true []
    | ']' :: _rest => if openBracket && !acc.isEmpty then some (String.ofList acc.reverse) else none
    | c :: rest => if openBracket then go rest true (c :: acc) else go rest false acc

/-- Tags are three lowercase letters, a dash, and digits: `[mcd-1]`, `[eld-10]`. -/
def isTag (s : String) : Bool :=
  match s.toList with
  | a :: b :: c :: '-' :: rest =>
      a.isAlpha && a.isLower && b.isAlpha && b.isLower && c.isAlpha && c.isLower &&
        !rest.isEmpty && rest.all (fun d => d.isDigit)
  | _ => false

/-- Left-associated chain, matching `toSexp`'s output for n-ary forms. -/
def foldLeft (init : Formula String String String) (rest : List (Formula String String String))
    (mk : Formula String String String → Formula String String String → Formula String String String) :
    Formula String String String :=
  List.foldl (fun acc x => mk acc x) init rest

/-- Parse a CLIF term. `scope` lists the quantifier variables in scope, innermost first.

Structural on the S-expression, but the recursive calls go through `mapM` over the
argument list, which Lean's structural-recursion checker cannot see. `partial` is safe
here (and axiom-free in this toolchain): the recursion is genuinely on sub-expressions,
and the parser is the untrusted side of the boundary — the round-trip gate is what
establishes that it does not mangle the axioms. -/
partial def parseTerm (scope : List String) (s : Sexp) : Except String (Term String String) := do
  match s with
  | .atom name =>
      if scope.any (· == name) then pure (Term.var name) else pure (Term.app name [])
  | .list (Sexp.atom head :: args) => pure (Term.app head (← args.mapM (parseTerm scope)))
  | .list _ => Except.error s!"malformed term: {Sexp.toText s}"

/-- Parse a CLIF formula. -/
partial def parseFormula (scope : List String) (s : Sexp) : Except String (Formula String String String) := do
  match s with
  | .atom "true" => pure Formula.tr
  | .atom "false" => pure Formula.fls
  | .atom name => Except.error s!"atomic formula needs a list form: {name}"
  | .list (Sexp.atom head :: args) =>
      match head with
      | "=" =>
          match args with
          | [a, b] => pure (Formula.eql (← parseTerm scope a) (← parseTerm scope b))
          | _ => Except.error s!"equality needs exactly two terms: {Sexp.toText s}"
      | "and" =>
          match args with
          | [] => Except.error s!"and needs at least one argument: {Sexp.toText s}"
          | [x] => parseFormula scope x          -- degenerate `(and p)` is just `p`
          | x :: rest =>
              pure (foldLeft (← parseFormula scope x) (← rest.mapM (parseFormula scope)) Formula.conj)
      | "or" =>
          match args with
          | [] => Except.error s!"or needs at least one argument: {Sexp.toText s}"
          | [x] => parseFormula scope x        -- degenerate `(or p)` is just `p`
          | x :: rest =>
              pure (foldLeft (← parseFormula scope x) (← rest.mapM (parseFormula scope)) Formula.disj)
      | "if" =>
          match args with
          | [a, b] => pure (Formula.impl (← parseFormula scope a) (← parseFormula scope b))
          | _ => Except.error s!"if needs exactly two arguments: {Sexp.toText s}"
      | "iff" =>
          match args with
          | [a, b] => pure (Formula.iffT (← parseFormula scope a) (← parseFormula scope b))
          | _ => Except.error s!"iff needs exactly two arguments: {Sexp.toText s}"
      | "not" =>
          match args with
          | [a] => pure (Formula.neg (← parseFormula scope a))
          | _ => Except.error s!"not needs exactly one argument: {Sexp.toText s}"
      | "forall" | "exists" =>
          let (vars, body) ← match args with
            | [Sexp.list vs, body] => pure (vs, body)
            | _ => Except.error s!"quantifier needs a variable list and a body: {Sexp.toText s}"
          let vs ← vars.mapM fun v => match v with
            | .atom name => pure name
            | .list _ => Except.error s!"quantifier variable must be an identifier: {Sexp.toText v}"
          if vs.isEmpty then Except.error s!"quantifier binds no variables: {Sexp.toText s}"
          -- Innermost binder must be the innermost in scope, so build scope right-to-left.
          let φ ← parseFormula (vs.reverse ++ scope) body
          pure (List.foldr (fun v body =>
            if head == "forall" then Formula.allv v body else Formula.exv v body) φ vs)
      | other =>
          if other.startsWith "cl:" then
            Except.error s!"unexpected wrapper form in formula position: {Sexp.toText s}"
          pure (Formula.rel other (← args.mapM (parseTerm scope)))
  | .list _ => Except.error s!"malformed formula: {Sexp.toText s}"

/-- Back to S-expressions, with the same normalization `parseFormula` applies: binary
conjunction/disjunction, grouped quantifier variables. -/
def Formula.toSexp (φ : Formula String String String) : Sexp := go [] true φ
where
  go (pending : List String) (isForall : Bool) (φ : Formula String String String) : Sexp :=
    let close (body : Sexp) : Sexp :=
      if pending.isEmpty then body
      else
        Sexp.list ([Sexp.atom (if isForall then "forall" else "exists"),
                    Sexp.list (pending.map Sexp.atom), body])
    match φ with
    | Formula.tr => close (Sexp.atom "true")
    | Formula.fls => close (Sexp.atom "false")
    | Formula.eql a b => close (Sexp.list [Sexp.atom "=", termSexp a, termSexp b])
    | Formula.rel r args => close (Sexp.list (Sexp.atom r :: args.map termSexp))
    | Formula.conj a b => close (Sexp.list [Sexp.atom "and", go [] true a, go [] true b])
    | Formula.disj a b => close (Sexp.list [Sexp.atom "or", go [] true a, go [] true b])
    | Formula.impl a b => close (Sexp.list [Sexp.atom "if", go [] true a, go [] true b])
    | Formula.iffT a b => close (Sexp.list [Sexp.atom "iff", go [] true a, go [] true b])
    | Formula.neg f => close (Sexp.list [Sexp.atom "not", go [] true f])
    | Formula.allv x b =>
        if pending.isEmpty || isForall then go (pending ++ [x]) true b
        else close (go [x] true b)
    | Formula.exv x b =>
        if pending.isEmpty || !isForall then go (pending ++ [x]) false b
        else close (go [x] false b)
  termSexp (t : Term String String) : Sexp :=
    match t with
    | Term.var x => Sexp.atom x
    | Term.app f [] => Sexp.atom f
    | Term.app f args => Sexp.list (Sexp.atom f :: args.map termSexp)

/-- Left-associated chain over already-normalized arguments: `(and a b c)` becomes
`(and (and a b) c)`, which is the shape of the binary AST. -/
def chainSexp (head : String) (args : List Sexp) : Sexp :=
  match args with
  | [] => Sexp.list [Sexp.atom head]
  | x :: rest => chainGo head x rest
where
  chainGo (head : String) (acc : Sexp) (xs : List Sexp) : Sexp :=
    match xs with
    | [] => acc
    | y :: ys => chainGo head (Sexp.list [Sexp.atom head, acc, y]) ys

/-- The structural form an S-expression must have for `toSexp` to reproduce it: n-ary
`and`/`or` left-associated, degenerate `(or p)` collapsed, quantifier variable lists
and everything else kept as written.

Recursion descends into argument lists, which are nested sub-expressions; Lean's
structural checker cannot see through the cons pattern, so this is `partial` (total in
fact, and the parser is the untrusted side of the boundary anyway). -/
partial def normalizeList : List Sexp → List Sexp
  | [] => []
  | Sexp.list (Sexp.atom "and" :: [x]) :: xs =>
      normalizeList [x] ++ normalizeList xs
  | Sexp.list (Sexp.atom "and" :: args) :: xs =>
      chainSexp "and" (normalizeList args) :: normalizeList xs
  | Sexp.list (Sexp.atom "or" :: [x]) :: xs =>
      normalizeList [x] ++ normalizeList xs
  | Sexp.list (Sexp.atom "or" :: args) :: xs =>
      chainSexp "or" (normalizeList args) :: normalizeList xs
  | Sexp.list items :: xs => Sexp.list (normalizeList items) :: normalizeList xs
  | x :: xs => x :: normalizeList xs

/-- The structural form of a single S-expression. -/
def normalizeSexp (s : Sexp) : Sexp :=
  match normalizeList [s] with
  | [r] => r
  | _ => s

/-- A CLIF axiom as it appears in an artifact: tag, human label, formula. -/
structure Axiom where
  tag : String
  label : String
  sexp : Sexp
  formula : Formula String String String
  deriving BEq

/-- Collect tagged axioms, rejecting malformed tagged bodies instead of silently
omitting them. This parser accepts only the CLIF fragment used by these files. -/
partial def collectAxioms (ss : List Sexp) : Except String (List Axiom) := do
  let mut result := []
  for s in ss do
    match s with
    | .atom _ => pure ()
    | .list (Sexp.atom "cl:comment" :: Sexp.atom label :: bodies) =>
      match extractTag label with
      | some tag =>
        if !isTag tag then throw s!"invalid axiom tag: {tag}"
        match bodies with
        | [body] =>
          let φ ← (parseFormula [] body).mapError (fun e => s!"[{tag}] {e}")
          result := result ++ [{ tag, label, sexp := body, formula := φ }]
        | _ => throw s!"[{tag}] expected exactly one formula body"
      | none => result := result ++ (← collectAxioms bodies)
    | .list xs => result := result ++ (← collectAxioms xs)
  pure result
