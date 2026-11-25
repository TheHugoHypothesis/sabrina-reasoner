import Logic.FOL.Parser

/-! A fuel-bounded, total CLIF formula translator. Unlike the runtime
partial parser, this definition reduces in the kernel. An exhausted budget
or unsupported form fails instead of silently producing a formula. -/
namespace Logic.FOL.CLTotal

def isReserved (s : String) : Bool :=
  match s.toList with
  | 'c' :: 'l' :: ':' :: _ => true
  | _ => false

def term : Nat → List String → Sexp → Option (Term String String)
  | 0, _, _ => none
  | _n+1, scope, .atom name =>
    if scope.any (· == name) then some (.var name) else some (.app name [])
  | n+1, scope, .list (.atom head :: args) =>
    (args.mapM (term n scope)).map (.app head)
  | _+1, _, _ => none

def formula : Nat → List String → Sexp → Option (Formula String String String)
  | 0, _, _ => none
  | n+1, scope, input => do
    match input with
    | .atom "true" => some .tr
    | .atom "false" => some .fls
    | .atom _ => none
    | .list (.atom head :: args) =>
      match head, args with
      | "=", [a,b] => some (.eql (← term n scope a) (← term n scope b))
      | "and", a :: rest =>
        some (foldLeft (← formula n scope a) (← rest.mapM (formula n scope)) Formula.conj)
      | "or", a :: rest =>
        some (foldLeft (← formula n scope a) (← rest.mapM (formula n scope)) Formula.disj)
      | "if", [a,b] => some (.impl (← formula n scope a) (← formula n scope b))
      | "iff", [a,b] => some (.iffT (← formula n scope a) (← formula n scope b))
      | "not", [a] => some (.neg (← formula n scope a))
      | "forall", [.list vars, body] | "exists", [.list vars, body] =>
        let vs ← vars.mapM Sexp.atom?
        if vs.isEmpty || vs.eraseDups.length != vs.length then none
        else
          let φ ← formula n (vs.reverse ++ scope) body
          some (vs.foldr (fun v b => if head == "forall" then .allv v b else .exv v b) φ)
      | "=", _ | "and", _ | "or", _ | "if", _ | "iff", _ | "not", _
      | "forall", _ | "exists", _ => none
      | _, _ =>
        if isReserved head then none
        else some (.rel head (← args.mapM (term n scope)))
    | _ => none

end Logic.FOL.CLTotal
