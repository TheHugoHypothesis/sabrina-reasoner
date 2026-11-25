import Sabrina.Graded.Semantics

namespace Sabrina.Graded

open ALC RoleChains

structure Problem where
  rules : RoleTheory
  chains : List Chain
  tbox : TBox
  root : Concept
  chars : RoleChars := {}
  deriving Repr

def Problem.nominals (p : Problem) : List String :=
  (p.root.nominals ++ p.tbox.flatMap fun ax => ax.sub.nominals ++ ax.sup.nominals).eraseDups

abbrev Problem.Sat (p : Problem) : Prop := ConceptSat p.rules p.chains p.tbox p.root p.chars

structure NominalGraph where
  graph : Graph
  nominals : List (String × graph.World) := []

def NominalGraph.nomVal (m : NominalGraph) (a : String) : m.graph.World :=
  (m.nominals.lookup a).getD ⟨0, Nat.zero_lt_succ _⟩

private theorem atLeast_filter_iff {α : Type} (xs : List α) (hx : xs.Nodup)
    (hall : ∀ x, x ∈ xs) (test : α → Bool) (n : Nat) :
    n ≤ (xs.filter test).length ↔ AtLeast n (fun x => test x = true) := by
  constructor
  · intro h
    refine ⟨(xs.filter test).take n, List.length_take_of_le h,
      ((List.take_sublist ..).nodup (List.filter_sublist.nodup hx)), ?_⟩
    exact fun _ hm => (List.mem_filter.mp (List.mem_of_mem_take hm)).2
  · rintro ⟨ys,hlen,hy,hp⟩
    rw [← hlen]
    exact hy.length_le_of_subset fun a ha => List.mem_filter.mpr ⟨hall a,hp a ha⟩

def eval (m : NominalGraph) (x : m.graph.World) : Concept → Bool
  | .top => true
  | .bottom => false
  | .lit p true => m.graph.atom p x
  | .lit p false => !m.graph.atom p x
  | .nom a true => x == m.nomVal a
  | .nom a false => x != m.nomVal a
  | .self r true => m.graph.edge r x x
  | .self r false => !m.graph.edge r x x
  | .conj a b => eval m x a && eval m x b
  | .disj a b => eval m x a || eval m x b
  | .some r c => m.graph.worlds.any fun y => m.graph.edge r x y && eval m y c
  | .all r c => m.graph.worlds.all fun y => !m.graph.edge r x y || eval m y c
  | .min n r c => decide (n ≤ (m.graph.worlds.filter fun y => m.graph.edge r x y && eval m y c).length)
  | .max n r c => !decide (n + 1 ≤ (m.graph.worlds.filter fun y => m.graph.edge r x y && eval m y c).length)

theorem eval_iff (m : NominalGraph) (x : m.graph.World) (c : Concept) :
    eval m x c = true ↔ Graded.holds m.graph.interpretation m.nomVal x c := by
  induction c generalizing x with
  | top | bottom => simp [eval, Graded.holds]
  | lit p sign => cases sign <;> simp [eval, Graded.holds, Graph.interpretation]
  | nom a sign => cases sign <;> simp [eval, Graded.holds] <;> exact Iff.rfl
  | self r sign => cases sign <;> simp [eval, Graded.holds, Graph.interpretation]
  | conj a b ha hb => simp only [eval, Graded.holds, Bool.and_eq_true, ha,hb]
  | disj a b ha hb => simp only [eval, Graded.holds, Bool.or_eq_true, ha,hb]
  | some r c ih =>
    simp [eval, Graded.holds, Graph.interpretation, List.any_eq_true, Graph.worlds, ih]
  | all r c ih =>
    simp only [eval, Graded.holds, Graph.interpretation, List.all_eq_true,
      Graph.worlds, List.mem_finRange, true_implies, Bool.or_eq_true, ih]
    constructor
    · intro h y hy
      exact (h y).resolve_left (by simp [hy])
    · intro h y
      by_cases he : m.graph.edge r x y = true
      · exact Or.inr (h y he)
      · exact Or.inl (by simpa using he)
  | min n r c ih =>
    simp only [eval, Graded.holds, decide_eq_true_eq]
    rw [atLeast_filter_iff m.graph.worlds (List.nodup_finRange _) List.mem_finRange]
    simp only [AtLeast, Bool.and_eq_true, ih, Graph.interpretation] <;> rfl
  | max n r c ih =>
    simp only [eval, Graded.holds, Bool.not_eq_true', decide_eq_false_iff_not]
    rw [atLeast_filter_iff m.graph.worlds (List.nodup_finRange _) List.mem_finRange]
    simp only [AtLeast, Bool.and_eq_true, ih, Graph.interpretation] <;> rfl

def evalOrientedRole (g : Graph) (r : OrientedRole) (x y : g.World) : Bool :=
  if r.2 then g.edge r.1 y x else g.edge r.1 x y

theorem evalOrientedRole_iff (g : Graph) (r : OrientedRole) (x y : g.World) :
    evalOrientedRole g r x y = true ↔ holdsRole g.interpretation r x y := by
  rcases r with ⟨r, _ | _⟩ <;> simp [evalOrientedRole, holdsRole, Graph.interpretation]

def checkRoleChars (chars : RoleChars) (g : Graph) : Bool :=
  chars.reflexive.all (fun r => g.worlds.all fun x => g.edge r x x) &&
  chars.irreflexive.all (fun r => g.worlds.all fun x => !g.edge r x x) &&
  chars.asymmetric.all (fun r => g.worlds.all fun x => g.worlds.all fun y => !(g.edge r x y && g.edge r y x)) &&
  chars.disjoint.all (fun p => g.worlds.all fun x => g.worlds.all fun y =>
    !(evalOrientedRole g p.1 x y && evalOrientedRole g p.2 x y))

theorem checkRoleChars_iff {chars : RoleChars} {g : Graph} :
    checkRoleChars chars g = true ↔ modelsRoleChars g.interpretation chars := by
  simp only [checkRoleChars, modelsRoleChars, Bool.and_eq_true, List.all_eq_true,
    Graph.worlds, List.mem_finRange, true_implies, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, evalOrientedRole_iff, Graph.interpretation]
  exact ⟨fun ⟨⟨⟨href, hirr⟩, hasym⟩, hdisj⟩ =>
      ⟨href, hirr, fun r hr x y hxy hyx => hasym r hr x y ⟨hxy, hyx⟩, hdisj⟩,
    fun ⟨href, hirr, hasym, hdisj⟩ =>
      ⟨⟨⟨href, hirr⟩, fun r hr x y ⟨hxy, hyx⟩ => hasym r hr x y hxy hyx⟩, hdisj⟩⟩

def checkModel (p : Problem) (m : NominalGraph) : Bool :=
  checkRoleAxioms p.rules p.chains m.graph &&
  checkRoleChars p.chars m.graph &&
  p.tbox.all (fun q => m.graph.worlds.all fun x => !eval m x q.sub || eval m x q.sup) &&
  m.graph.worlds.any (fun x => eval m x p.root)

theorem checkModel_iff {p : Problem} {m : NominalGraph} :
    checkModel p m = true ↔
      modelsRoles m.graph.interpretation p.rules ∧ modelsChains m.graph.interpretation p.chains ∧
      modelsRoleChars m.graph.interpretation p.chars ∧
      Graded.models m.graph.interpretation m.nomVal p.tbox ∧
      ∃ x, Graded.holds m.graph.interpretation m.nomVal x p.root := by
  simp only [checkModel, Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨⟨⟨hg, hrc⟩, ht⟩, ⟨x, _, hx⟩⟩
    have ⟨hr, hc⟩ := checkRoleAxioms_iff.mp hg
    refine ⟨hr, hc, checkRoleChars_iff.mp hrc, ?_, x, (eval_iff m x p.root).mp hx⟩
    intro q hq y hy
    have hh := ht q hq y (List.mem_finRange _)
    rw [(eval_iff m y q.sub).mpr hy] at hh
    exact (eval_iff m y q.sup).mp (by simpa using hh)
  · rintro ⟨hr, hc, hrc, ht, x, hx⟩
    refine ⟨⟨⟨checkRoleAxioms_iff.mpr ⟨hr, hc⟩, checkRoleChars_iff.mpr hrc⟩, ?_⟩,
      x, List.mem_finRange _, (eval_iff m x p.root).mpr hx⟩
    intro q hq y _
    cases he : eval m y q.sub
    · simp
    · simp [(eval_iff m y q.sup).mpr (ht q hq y ((eval_iff m y q.sub).mp he))]

theorem checkModel_sound {p : Problem} {m : NominalGraph} (h : checkModel p m = true) : p.Sat :=
  ⟨m.graph.interpretation, m.nomVal, checkModel_iff.mp h⟩

end Sabrina.Graded
