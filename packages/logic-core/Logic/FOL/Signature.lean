import Logic.FOL.Syntax

/-! Arity checking for the first-order fragment. The signature describes observed
uses; it does not add typing axioms or restrict CL's variable-arity semantics. -/
namespace Logic.FOL

structure Signature (R F : Type) where
  relationArity : R → Option Nat
  functionArity : F → Option Nat

mutual
/-- A term uses only declared function symbols at their declared arity. -/
def Term.wellFormed (sig : Signature R F) : Term F V → Bool
  | .var _ => true
  | .app f args => sig.functionArity f == some args.length && termsWellFormed sig args

def termsWellFormed (sig : Signature R F) : List (Term F V) → Bool
  | [] => true
  | t :: ts => t.wellFormed sig && termsWellFormed sig ts
end

/-- A formula uses only symbols declared at the given arities. -/
def Formula.wellFormed (sig : Signature R F) : Formula R F V → Bool
  | .tr | .fls => true
  | .eql a b => a.wellFormed sig && b.wellFormed sig
  | .rel r args => sig.relationArity r == some args.length && termsWellFormed sig args
  | .conj a b | .disj a b | .impl a b | .iffT a b => a.wellFormed sig && b.wellFormed sig
  | .neg a | .allv _ a | .exv _ a => a.wellFormed sig

end Logic.FOL
