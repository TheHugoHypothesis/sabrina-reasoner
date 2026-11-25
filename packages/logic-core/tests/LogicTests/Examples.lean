import Logic.Proof.Derivation

namespace Logic.Proof
open Logic.FOL

/-- A two-step implication chain, derived syntactically. -/
theorem implication_chain [DecidableEq V] [Fresh V]
    (a b c : Formula R F V) :
    Derives [.impl a b, .impl b c] (.impl a c) := by
  apply Derives.impIntro
  have ha : Derives [a, .impl a b, .impl b c] a :=
    Derives.assumption (by simp)
  have hab : Derives [a, .impl a b, .impl b c] (.impl a b) :=
    Derives.assumption (by simp)
  have hbc : Derives [a, .impl a b, .impl b c] (.impl b c) :=
    Derives.assumption (by simp)
  exact Derives.impElim hbc (Derives.impElim hab ha)

/-- Universal instantiation followed by existential introduction. -/
theorem universal_implies_existential [DecidableEq V] [Fresh V]
    (x : V) (body : Formula R F V) (t : Term F V) :
    Derives [.allv x body] (.exv x body) :=
  Derives.existsIntro t (Derives.allElim t (Derives.assumption (by simp)))

theorem implication_chain_semantic [DecidableEq V] [Fresh V]
    (a b c : Formula R F V) :
    Entails [.impl a b, .impl b c] (.impl a c) :=
  sound (implication_chain a b c)

/-- Disjunction elimination: commutativity of `∨`. -/
theorem or_comm_derives [DecidableEq V] [Fresh V] (a b : Formula R F V) :
    Derives [.disj a b] (.disj b a) :=
  Derives.orElim (a := a) (b := b) (Derives.assumption (by simp))
    (Derives.orRight (Derives.assumption (by simp)))
    (Derives.orLeft (Derives.assumption (by simp)))

/-- Classical reasoning: double-negation elimination. -/
theorem double_neg_elim [DecidableEq V] [Fresh V] (a : Formula R F V) :
    Derives [.neg (.neg a)] a :=
  Derives.classical
    (Derives.negElim (a := .neg a) (Derives.assumption (by simp))
      (Derives.assumption (by simp)))

/-- Excluded middle, via classical reasoning and disjunction introduction. -/
theorem excluded_middle [DecidableEq V] [Fresh V] (a : Formula R F V) :
    Derives [] (.disj a (.neg a)) := by
  apply Derives.classical
  have hn : Derives [.neg (.disj a (.neg a))] (.neg (.disj a (.neg a))) :=
    Derives.assumption (by simp)
  have hna : Derives [.neg (.disj a (.neg a))] (.neg a) := by
    apply Derives.negIntro
    refine Derives.negElim (a := .disj a (.neg a)) (weaken hn (by simp)) ?_
    exact Derives.orLeft (Derives.assumption (by simp))
  exact Derives.negElim hn (Derives.orRight hna)

/-- Biconditional introduction and elimination: `(a ↔ b) ⊢ (b ↔ a)`. -/
theorem iff_swap [DecidableEq V] [Fresh V] (a b : Formula R F V) :
    Derives [.iffT a b] (.iffT b a) := by
  have h : ∀ x : Formula R F V, Derives [x, .iffT a b] (.iffT a b) :=
    fun _ => Derives.assumption (by simp)
  refine Derives.iffIntro ?_ ?_
  · exact Derives.iffRight (a := a) (b := b) (h _) (Derives.assumption (by simp))
  · exact Derives.iffLeft (a := a) (b := b) (h _) (Derives.assumption (by simp))

/-- Context extension: an unused premise does not matter. -/
theorem extra_premise [DecidableEq V] [Fresh V] (a b : Formula R F V) :
    Derives [b, .impl a a] (.impl a a) :=
  weaken (Γ := []) (Derives.impIntro (Derives.assumption (by simp))) (by simp)

theorem exchange_cut [DecidableEq V] [Fresh V] (a b : Formula R F V) :
    Derives [a, b] (.conj b a) :=
  Derives.andIntro (Derives.assumption (by simp)) (Derives.assumption (by simp))

/-- Exchange of the first two premises. -/
theorem exchange_example [DecidableEq V] [Fresh V] (a b : Formula R F V) :
    Derives [b, a] (.conj b a) :=
  exchange (exchange_cut a b)

end Logic.Proof
