import Logic.FOL.Syntax

/-!
# CLIF printer

`toClif` renders a formula in Common Logic Interchange Format. Stage 1's faithfulness
gate is "parse the printed text and get the same formula back", checked over all 379
upstream axioms in `lake exe bfo-roundtrip`; the printer therefore has to reproduce
CLIF: prefix notation (`(= x y)`), grouped binder lists (`(forall (a b t) …)`, which is
how the BFO files write them), n-ary `and`/`or`, bare nullary symbols, and symbol names
verbatim.

Symbols are abstract here; naming functions supply the CLIF spelling, so one printer
serves both the `String`-coded parser output and the finite-enumeration encoding used
for model checking.

`toClifWith` is `partial`: it collects a binder run and a conjunction chain before
emitting them, and Lean's structural checker cannot see that the collected pieces are
subformulas. Printing is on the untrusted side of the boundary — a wrong printer shows
up as a round-trip failure, and the definition is axiom-free either way.
-/

namespace Logic.FOL

def Term.toClif (varName : V → String) (fnName : F → String) : Term F V → String
  | Term.var x => varName x
  | Term.app f [] => fnName f   -- CLIF writes nullary symbols bare
  | Term.app f args =>
      "(" ++ fnName f ++ " "
        ++ String.intercalate " " (args.map (Term.toClif varName fnName)) ++ ")"

def clifQuant (isForall : Bool) : String := if isForall then "forall" else "exists"

/-- The operands of a left-nested conjunction chain, in source order. CLIF is n-ary
(`(and a b c)`; up to six arguments in these files) while the AST is binary, so the
printer flattens the left spine back. A right-nested chain is left as CLIF wrote it. -/
def Formula.andOperands : Formula R F V → List (Formula R F V)
  | Formula.conj a b => Formula.andOperands a ++ [b]
  | φ => [φ]

/-- Same for disjunction. -/
def Formula.orOperands : Formula R F V → List (Formula R F V)
  | Formula.disj a b => Formula.orOperands a ++ [b]
  | φ => [φ]

/-- Rendering with an open binder group: `pending` are the quantifier variables
collected so far and `isForall` the kind of that run. -/
partial def Formula.toClifWith
    (varName : V → String) (relName : R → String) (fnName : F → String)
    (pending : List V) (isForall : Bool) : Formula R F V → String
  | Formula.tr => close pending isForall "true"
  | Formula.fls => close pending isForall "false"
  | Formula.eql a b =>
      close pending isForall
        ("(= " ++ Term.toClif varName fnName a ++ " " ++ Term.toClif varName fnName b ++ ")")
  | Formula.rel r args =>
      close pending isForall
        ("(" ++ relName r ++ " "
          ++ String.intercalate " " (args.map (Term.toClif varName fnName)) ++ ")")
  | Formula.conj a b =>
      close pending isForall
        ("(and " ++ String.intercalate " "
          ((Formula.andOperands (Formula.conj a b)).map
            (fun x => Formula.toClifWith varName relName fnName [] true x)) ++ ")")
  | Formula.disj a b =>
      close pending isForall
        ("(or " ++ String.intercalate " "
          ((Formula.orOperands (Formula.disj a b)).map
            (fun x => Formula.toClifWith varName relName fnName [] true x)) ++ ")")
  | Formula.impl a b =>
      close pending isForall
        ("(if " ++ Formula.toClifWith varName relName fnName [] true a
          ++ " " ++ Formula.toClifWith varName relName fnName [] true b ++ ")")
  | Formula.iffT a b =>
      close pending isForall
        ("(iff " ++ Formula.toClifWith varName relName fnName [] true a
          ++ " " ++ Formula.toClifWith varName relName fnName [] true b ++ ")")
  | Formula.neg f =>
      close pending isForall ("(not " ++ Formula.toClifWith varName relName fnName [] true f ++ ")")
  | Formula.allv x b =>
      if pending.isEmpty || isForall then
        Formula.toClifWith varName relName fnName (pending ++ [x]) true b
      else
        "(" ++ clifQuant isForall ++ " (" ++ clifVars varName pending ++ ") "
          ++ Formula.toClifWith varName relName fnName [x] true b ++ ")"
  | Formula.exv x b =>
      if pending.isEmpty || !isForall then
        Formula.toClifWith varName relName fnName (pending ++ [x]) false b
      else
        "(" ++ clifQuant isForall ++ " (" ++ clifVars varName pending ++ ") "
          ++ Formula.toClifWith varName relName fnName [x] false b ++ ")"
where
  clifVars (varName : V → String) (vs : List V) : String := String.intercalate " " (vs.map varName)
  close (pending : List V) (isForall : Bool) (body : String) : String :=
    if pending.isEmpty then body
    else "(" ++ clifQuant isForall ++ " (" ++ clifVars varName pending ++ ") " ++ body ++ ")"

/-- A formula rendered as CLIF. -/
def Formula.toClif
    (varName : V → String) (relName : R → String) (fnName : F → String) : Formula R F V → String :=
  Formula.toClifWith varName relName fnName [] true

end Logic.FOL
