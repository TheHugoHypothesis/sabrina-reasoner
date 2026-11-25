import Sabrina.RoleChains.Model
import Sabrina.RoleChains.TransitivePaths

namespace Sabrina.RoleChains.TransitivePaths

open Sabrina.ALC

theorem wordPath_append (i : Interpretation) (word tail : List OrientedRole)
    (x z : i.Domain) :
    WordPath i (word ++ tail) x z ↔ ∃ y, WordPath i word x y ∧ WordPath i tail y z := by
  induction word generalizing x with
  | nil => simp [WordPath]
  | cons r word ih =>
    constructor
    · rintro ⟨v, hv, h⟩
      obtain ⟨y, hw, ht⟩ := (ih v).mp h
      exact ⟨y, ⟨v, hv, hw⟩, ht⟩
    · rintro ⟨y, ⟨v, hv, hw⟩, ht⟩
      exact ⟨v, hv, (ih v).mpr ⟨y, hw, ht⟩⟩

def flipWord (w : List OrientedRole) : List OrientedRole := (w.map converse).reverse

theorem wordPath_flip {i : Interpretation} {w : List OrientedRole} {x y : i.Domain}
    (h : WordPath i w x y) : WordPath i (flipWord w) y x := by
  induction w generalizing x with
  | nil => exact h.symm
  | cons r rest ih =>
    obtain ⟨z, hz, hr⟩ := h
    simp only [flipWord, List.map_cons, List.reverse_cons]
    refine (wordPath_append i _ _ _ _).mpr ⟨z, ih hr, x, ?_, rfl⟩
    rcases r with ⟨r, _ | _⟩ <;> exact hz

theorem Derives.flip {rules ts word r} (h : Derives rules ts word r) :
    Derives rules ts (flipWord word) (converse r) := by
  induction h with
  | letter r => exact Derives.letter (converse r)
  | promote h _ ih => exact Derives.promote (mirrored_flip h) ih
  | @join w v r hr _ _ ih₁ ih₂ =>
    simpa only [flipWord, List.map_append, List.reverse_append] using
      Derives.join (r := converse r) hr ih₂ ih₁

def TransitiveRoles (i : Interpretation) (ts : List String) : Prop :=
  ∀ r ∈ ts, ∀ x y z, i.role r x y → i.role r y z → i.role r x z

private theorem transitive_oriented {i : Interpretation} {ts : List String}
    (ht : TransitiveRoles i ts) {r : OrientedRole} (hr : r.1 ∈ ts) {x y z : i.Domain}
    (h₁ : holdsRole i r x y) (h₂ : holdsRole i r y z) : holdsRole i r x z := by
  rcases r with ⟨r, _ | _⟩
  · exact ht r hr x y z h₁ h₂
  · exact ht r hr z y x h₂ h₁

theorem Derives.sound {rules ts word r} (h : Derives rules ts word r)
    {i : Interpretation} (hm : modelsRoles i rules) (ht : TransitiveRoles i ts)
    {x y : i.Domain} (hp : WordPath i word x y) : holdsRole i r x y := by
  induction h generalizing x y with
  | letter r =>
    obtain ⟨z, hz, he⟩ := hp
    change z = y at he
    exact he ▸ hz
  | promote hr _ ih => exact modelsMirrored hm _ _ hr x y (ih hp)
  | join h _ _ ih₁ ih₂ =>
    obtain ⟨z, hz, hy⟩ := (wordPath_append i _ _ _ _).mp hp
    exact transitive_oriented ht h (ih₁ hz) (ih₂ hy)

def DerivedEdge (rules : RoleTheory) (ts : List String) (i : Interpretation)
    (r : OrientedRole) (x y : i.Domain) : Prop :=
  ∃ word, Derives rules ts word r ∧ WordPath i word x y

theorem derivedEdge_flip {rules ts i r x y} (h : DerivedEdge rules ts i r x y) :
    DerivedEdge rules ts i (converse r) y x := by
  obtain ⟨word, hd, hp⟩ := h
  exact ⟨flipWord word, hd.flip, wordPath_flip hp⟩

def complete (i : Interpretation) (rules : RoleTheory) (ts : List String) : Interpretation :=
  {i with role := fun r x y => DerivedEdge rules ts i (r,false) x y}

theorem holdsRole_complete (i : Interpretation) (rules : RoleTheory) (ts : List String)
    (r : OrientedRole) (x y : i.Domain) :
    holdsRole (complete i rules ts) r x y ↔ DerivedEdge rules ts i r x y := by
  rcases r with ⟨r, _ | _⟩
  · rfl
  · exact ⟨fun h => derivedEdge_flip (r := (r,false)) h,
      fun h => derivedEdge_flip (r := (r,true)) h⟩

theorem complete_extension (i : Interpretation) (rules : RoleTheory) (ts : List String)
    (r : String) (x y : i.Domain) (h : i.role r x y) : (complete i rules ts).role r x y :=
  ⟨[(r,false)], Derives.letter _, y, h, rfl⟩

theorem complete_modelsRoles (i : Interpretation) (rules : RoleTheory) (ts : List String) :
    modelsRoles (complete i rules ts) rules := by
  intro r s h x y hr
  obtain ⟨word, hd, hp⟩ := (holdsRole_complete i rules ts r x y).mp hr
  exact (holdsRole_complete i rules ts s x y).mpr
    ⟨word, Derives.promote (List.mem_append_left _ h) hd, hp⟩

theorem complete_transitive (i : Interpretation) (rules : RoleTheory) (ts : List String) :
    TransitiveRoles (complete i rules ts) ts := by
  intro r hr x y z hx hy
  obtain ⟨word, hd₁, hp₁⟩ := hx
  obtain ⟨tail, hd₂, hp₂⟩ := hy
  exact ⟨word ++ tail, Derives.join hr hd₁ hd₂, (wordPath_append i _ _ _ _).mpr ⟨y, hp₁, hp₂⟩⟩

private theorem wordPath_mono {i j : Interpretation} (domain : j.Domain = i.Domain)
    (lift : ∀ r x y, i.role r x y → j.role r (domain.symm ▸ x) (domain.symm ▸ y))
    {word : List OrientedRole} {x y : i.Domain} (h : WordPath i word x y) :
    WordPath j word (domain.symm ▸ x) (domain.symm ▸ y) := by
  induction word generalizing x with
  | nil =>
    change x = y at h
    rw [h]
    rfl
  | cons r word ih =>
    obtain ⟨z, hz, hp⟩ := h
    refine ⟨domain.symm ▸ z, ?_, ih hp⟩
    rcases r with ⟨r, _ | _⟩
    · exact lift r x z hz
    · exact lift r z x hz

/-- Every extension satisfying the role axioms contains the completed edges. -/
theorem complete_least {i j : Interpretation} (domain : j.Domain = i.Domain)
    (lift : ∀ r x y, i.role r x y → j.role r (domain.symm ▸ x) (domain.symm ▸ y))
    {rules ts} (hm : modelsRoles j rules) (ht : TransitiveRoles j ts)
    {r : String} {x y : i.Domain} (h : (complete i rules ts).role r x y) :
    j.role r (domain.symm ▸ x) (domain.symm ▸ y) := by
  obtain ⟨_, hd, hp⟩ := h
  exact hd.sound hm ht (wordPath_mono domain lift hp)

/-- A local invariant for each repeat state propagates a universal condition
    along all accepting paths, including cycles. The invariant starts after
    the first edge because this automaton accepts only nonempty paths. -/
def Automaton.guards (a : Automaton) (i : Interpretation) (x : i.Domain)
    (good : i.Domain → Prop) : Prop :=
  (∀ r ∈ a.singletons, ∀ y, holdsRole i r x y → good y) ∧
  ∀ letters ∈ a.repeats, ∃ inv : i.Domain → Prop,
    (∀ r ∈ letters, ∀ y, holdsRole i r x y → inv y) ∧
    (∀ r ∈ letters, ∀ z y, inv z → holdsRole i r z y → inv y) ∧
    ∀ y, inv y → good y

theorem Automaton.guards_iff (a : Automaton) (i : Interpretation) (x : i.Domain)
    (good : i.Domain → Prop) :
    a.guards i x good ↔
      ∀ word y, a.accepts word = true → WordPath i word x y → good y := by
  constructor
  · rintro ⟨hs, hloop⟩ word y hw hp
    cases word with
    | nil => simp [Automaton.accepts] at hw
    | cons r tail =>
      simp only [Automaton.accepts, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff,
        List.contains_iff_mem, List.any_eq_true, List.all_eq_true] at hw
      obtain ⟨z, hz, htail⟩ := hp
      rcases hw with ⟨rfl, hr⟩ | ⟨letters, hm, hletters⟩
      · change z = y at htail
        exact htail ▸ hs r hr z hz
      · obtain ⟨inv, hstart, hstep, hgood⟩ := hloop letters hm
        have finish : ∀ v, (∀ s ∈ v, s ∈ letters) → ∀ u, inv u →
            WordPath i v u y → inv y := by
          intro v
          induction v with
          | nil =>
            intro _ u hu he
            change u = y at he
            exact he ▸ hu
          | cons s rest ih =>
            rintro hl u hu ⟨v, hv, hrest⟩
            exact ih (fun t ht => hl t (List.mem_cons_of_mem _ ht)) v
              (hstep s (hl s (List.mem_cons_self ..)) u v hu hv) hrest
        exact hgood y (finish tail (fun s hs => hletters s (List.mem_cons_of_mem _ hs)) z
          (hstart r (hletters r (List.mem_cons_self ..)) z hz) htail)
  · intro h
    refine ⟨fun r hr y he => h [r] y (by simp [Automaton.accepts, hr]) ⟨y, he, rfl⟩, ?_⟩
    intro letters hm
    let inv := fun y => ∃ word, word ≠ [] ∧ (∀ r ∈ word, r ∈ letters) ∧ WordPath i word x y
    refine ⟨inv, ?_, ?_, ?_⟩
    · intro r hr y he
      exact ⟨[r], by simp, by simpa, y, he, rfl⟩
    · rintro r hr z y ⟨word, hn, hl, hp⟩ he
      exact ⟨word ++ [r], by simp, fun s hs => (List.mem_append.mp hs).elim (hl s)
        (fun hs => (List.mem_singleton.mp hs).symm ▸ hr),
        (wordPath_append i _ _ _ _).mpr ⟨z, hp, y, he, rfl⟩⟩
    · rintro y ⟨word, hn, hl, hp⟩
      refine h word y ?_ hp
      cases word with
      | nil => exact (hn rfl).elim
      | cons r tail =>
        simp only [Automaton.accepts, Bool.or_eq_true]
        exact Or.inr (List.any_eq_true.mpr
          ⟨letters, hm, List.all_eq_true.mpr fun s hs => List.contains_iff_mem.mpr (hl s hs)⟩)

/-- Existing witnesses and propagated negative existential constraints are
    sufficient to keep every query and TBox subformula true at the same worlds. -/
theorem holds_complete_iff {i : Interpretation} {rules : RoleTheory} {ts : List String}
    {tbox : TBox} {root : Concept}
    (guard : ∀ r c, .some r c ∈ closure tbox root → ∀ x y,
      DerivedEdge rules ts i (r,false) x y → holds i y c → holds i x (.some r c))
    (x : i.Domain) {c : Concept} (hc : c ∈ closure tbox root) :
    holds (complete i rules ts) x c ↔ holds i x c := by
  induction c generalizing x with
  | atom | top => rfl
  | neg c ih => simp only [holds, ih x (neg_mem_closure hc)]
  | conj a b iha ihb =>
    obtain ⟨ha,hb⟩ := conj_mem_closure hc
    simp only [holds, iha x ha, ihb x hb]
  | some r c ih =>
    have hc' := some_mem_closure hc
    constructor
    · rintro ⟨y, hy, hh⟩
      exact guard r c hc x y hy ((ih y hc').mp hh)
    · rintro ⟨y, hy, hh⟩
      exact ⟨y, complete_extension i rules ts r x y hy, (ih y hc').mpr hh⟩

theorem holds_complete_of_automatonGuards {i : Interpretation} {rules : RoleTheory}
    {ts : List String} {tbox : TBox} {root : Concept}
    (guards : ∀ r c, .some r c ∈ closure tbox root → ∀ x,
      ¬ holds i x (.some r c) → (compile rules ts (r,false)).guards i x (fun y => ¬ holds i y c))
    (x : i.Domain) {c : Concept} (hc : c ∈ closure tbox root) :
    holds (complete i rules ts) x c ↔ holds i x c := by
  apply holds_complete_iff _ x hc
  intro r d hd u v he hv
  classical
  apply Classical.byContradiction
  intro hn
  obtain ⟨word, hw, hp⟩ := he
  exact (Automaton.guards_iff _ _ _ _).mp (guards r d hd u hn)
    word v ((compile_correct _ _ _ _).mpr hw) hp hv

private def alphabetPairs (g : RoleChains.Graph) (letters : List OrientedRole) :
    List (g.World × g.World) :=
  g.worlds.flatMap fun x => g.worlds.filterMap fun y =>
    if letters.any (fun r => g.oriented r x y) then some (x,y) else none

private theorem mem_alphabetPairs {g : RoleChains.Graph} {letters : List OrientedRole}
    {x y : g.World} :
    (x,y) ∈ alphabetPairs g letters ↔ ∃ r ∈ letters, holdsRole g.interpretation r x y := by
  simp only [alphabetPairs, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨a, _, b, _, h⟩
    split at h
    · rename_i ht
      have he := Option.some.inj h
      cases he
      obtain ⟨r, hr, hp⟩ := List.any_eq_true.mp ht
      exact ⟨r, hr, (g.oriented_iff r x y).mp hp⟩
    · simp at h
  · rintro ⟨r, hr, hp⟩
    have ht : letters.any (fun t => g.oriented t x y) = true :=
      List.any_eq_true.mpr ⟨r, hr, (g.oriented_iff r x y).mpr hp⟩
    exact ⟨x, List.mem_finRange _, y, List.mem_finRange _, by simp [ht]⟩

private def LoopPath (g : RoleChains.Graph) (letters : List OrientedRole) (x y : g.World) : Prop :=
  ∃ word, word ≠ [] ∧ (∀ r ∈ word, r ∈ letters) ∧ WordPath g.interpretation word x y

private theorem mem_loop {g : RoleChains.Graph} {letters : List OrientedRole} {x y : g.World} :
    (x,y) ∈ ALCH.close (alphabetPairs g letters) ↔ LoopPath g letters x y := by
  constructor
  · apply ALCH.close_sound
    · intro a b hab
      obtain ⟨r, hr, h⟩ := mem_alphabetPairs.mp hab
      exact ⟨[r], by simp, by simpa, b, h, rfl⟩
    · rintro a b c ⟨w, hw, hn, hp⟩ ⟨v, hv, hm, hq⟩
      exact ⟨w ++ v, by simp [hw], fun r hr => (List.mem_append.mp hr).elim (hn r) (hm r),
        (wordPath_append g.interpretation _ _ _ _).mpr ⟨b,hp,hq⟩⟩
  · rintro ⟨word, hw, hs, hp⟩
    induction word generalizing x with
    | nil => exact (hw rfl).elim
    | cons r tail ih =>
      obtain ⟨z, hr, h⟩ := hp
      have hz := ALCH.mem_close (mem_alphabetPairs.mpr ⟨r, hs r (List.mem_cons_self ..), hr⟩)
      by_cases ht : tail = []
      · subst tail
        change z = y at h
        exact h ▸ hz
      · exact ALCH.close_trans hz (ih ht (fun s hs' => hs s (List.mem_cons_of_mem _ hs')) h)

/-- Evaluate the automaton on a finite graph by relation closure on each loop
    alphabet. This avoids enumerating words of unbounded length. -/
def Automaton.pairs (a : Automaton) (g : RoleChains.Graph) : List (g.World × g.World) :=
  (alphabetPairs g a.singletons ++ a.repeats.flatMap (fun rs => ALCH.close (alphabetPairs g rs))).eraseDups

theorem mem_compile_pairs (g : RoleChains.Graph) (rules : RoleTheory) (ts : List String)
    (r : OrientedRole) (x y : g.World) :
    (x,y) ∈ (compile rules ts r).pairs g ↔ DerivedEdge rules ts g.interpretation r x y := by
  simp only [Automaton.pairs, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
    mem_alphabetPairs, mem_loop]
  constructor
  · rintro (⟨s, hs, he⟩ | ⟨letters, hletters, word, hn, ha, hp⟩)
    · have hd := (compile_correct rules ts [s] r).mp (by simp [Automaton.accepts, hs])
      exact ⟨[s], hd, y, he, rfl⟩
    · cases word with
      | nil => exact (hn rfl).elim
      | cons s rest =>
        have hd := (compile_correct rules ts (s :: rest) r).mp (by
          simp only [Automaton.accepts, Bool.or_eq_true]
          exact Or.inr (List.any_eq_true.mpr
            ⟨letters, hletters, List.all_eq_true.mpr fun l hl => List.contains_iff_mem.mpr (ha l hl)⟩))
        exact ⟨s :: rest, hd, hp⟩
  · rintro ⟨word, hd, hp⟩
    have ha := (compile_correct rules ts word r).mpr hd
    cases word with
    | nil => simp [Automaton.accepts] at ha
    | cons s rest =>
      simp only [Automaton.accepts, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff,
        List.contains_iff_mem, List.any_eq_true, List.all_eq_true] at ha
      rcases ha with ⟨rfl, hs⟩ | ⟨letters, hletters, hw⟩
      · obtain ⟨z, hz, he⟩ := hp
        change z = y at he
        exact Or.inl ⟨s, hs, he ▸ hz⟩
      · exact Or.inr ⟨letters, hletters, s :: rest, by simp, hw, hp⟩

/-- Complete the requested named relations, retaining all original facts. -/
def completeGraph (g : RoleChains.Graph) (rules : RoleTheory) (ts names : List String) :
    RoleChains.Graph :=
  let derived : List (String × g.World × g.World) := names.eraseDups.flatMap fun r =>
    ((compile rules ts (r,false)).pairs g).map fun pair => (r,pair.1,pair.2)
  { g with edges := (g.edges ++ derived).eraseDups }

theorem completeGraph_edge_iff (g : RoleChains.Graph) (rules : RoleTheory) (ts names : List String)
    {r : String} (hr : r ∈ names) (x y : g.World) :
    (completeGraph g rules ts names).edge r x y = true ↔
      (complete g.interpretation rules ts).role r x y := by
  change ((g.edges ++ names.eraseDups.flatMap (fun s =>
    ((compile rules ts (s,false)).pairs g).map fun pair => (s,pair.1,pair.2))).eraseDups.contains
      (r,x,y)) = true ↔ DerivedEdge rules ts g.interpretation (r,false) x y
  simp only [List.contains_iff_mem, List.mem_eraseDups,
    List.mem_append, List.mem_flatMap, List.mem_map]
  constructor
  · rintro (he | ⟨s, _, ⟨a,b⟩, hab, eq⟩)
    · exact complete_extension g.interpretation rules ts r x y (List.contains_iff_mem.mpr he)
    · simp only [Prod.mk.injEq] at eq
      change s = r ∧ a = x ∧ b = y at eq
      obtain ⟨rfl, rfl, rfl⟩ := eq
      exact (mem_compile_pairs g rules ts _ _ _).mp hab
  · intro h
    exact Or.inr ⟨r, hr, (x,y), (mem_compile_pairs g rules ts _ _ _).mpr h, rfl⟩

private theorem completeGraph_holdsRole_iff (g : RoleChains.Graph) (rules : RoleTheory)
    (ts names : List String) {r : OrientedRole} (hr : r.1 ∈ names) (x y : g.World) :
    holdsRole (completeGraph g rules ts names).interpretation r x y ↔
      holdsRole (complete g.interpretation rules ts) r x y := by
  rcases r with ⟨r, _ | _⟩
  · exact completeGraph_edge_iff g rules ts names hr x y
  · exact completeGraph_edge_iff g rules ts names hr y x

/-- Completion satisfies every role axiom as soon as the signature includes
    the roles used in those axioms. -/
theorem completeGraph_roles (g : RoleChains.Graph) (rules : RoleTheory) (ts names : List String)
    (hroles : ∀ r s : OrientedRole, (r,s) ∈ rules → r.1 ∈ names ∧ s.1 ∈ names)
    (hts : ts ⊆ names) :
    modelsRoles (completeGraph g rules ts names).interpretation rules ∧
      TransitiveRoles (completeGraph g rules ts names).interpretation ts := by
  constructor
  · intro r s hrs x y h
    obtain ⟨hr, hs⟩ := hroles r s hrs
    exact (completeGraph_holdsRole_iff g rules ts names hs x y).mpr
      (complete_modelsRoles g.interpretation rules ts r s hrs x y
        ((completeGraph_holdsRole_iff g rules ts names hr x y).mp h))
  · intro r hr x y z hx hy
    have edge := completeGraph_edge_iff g rules ts names (hts hr)
    exact (edge x z).mpr (complete_transitive g.interpretation rules ts r hr x y z
      ((edge x y).mp hx) ((edge y z).mp hy))

end Sabrina.RoleChains.TransitivePaths
