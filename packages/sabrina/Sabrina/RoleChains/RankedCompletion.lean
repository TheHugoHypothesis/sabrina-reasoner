import Sabrina.RoleChains.RankedCompiler

namespace Sabrina.RoleChains.RankedPaths

open Sabrina.ALC
open TransitivePaths (Below WordPath wordPath_append flipWord wordPath_flip)
open PathRegex (Segments)

private theorem segments_flip (L : OrientedRole → Language) (body w : Word)
    (h : Segments (body.map fun r u => L (converse r) (flipWord u)) w) :
    Segments ((flipWord body).map L) (flipWord w) := by
  induction body generalizing w with
  | nil => cases h; exact .nil
  | cons s tail ih =>
    cases h with
    | @cons _ _ u v hu hv =>
      have hs : flipWord (s :: tail) = flipWord tail ++ [converse s] := by
        simp [flipWord]
      rw [hs, flipWord_append, List.map_append]
      exact segments_append.mpr ⟨_,_,ih _ hv,segments_single.mpr hu,rfl⟩

theorem Generated.flip {rules chains r w} (h : Generated rules (normalize chains) r w) :
    Generated rules (normalize chains) (converse r) (flipWord w) := by
  intro L hc
  refine h (fun s u => L (converse s) (flipWord u)) ⟨?_,?_,?_⟩
  · intro s
    exact hc.letter (converse s)
  · intro s t u he ht
    exact hc.lift he.flip ht
  · intro c u hm hu
    have hh := segments_flip L _ _ hu
    apply hc.rule (normalize_flip hm)
    change Segments ((c.pattern.flip.body (converse c.head)).map L) (flipWord u)
    rwa [Pattern.flip_body]

private theorem wordPath_single {i : Interpretation} {r : OrientedRole} {x y : i.Domain} :
    WordPath i [r] x y ↔ holdsRole i r x y := by
  constructor
  · rintro ⟨z,hz,he⟩
    change z = y at he
    exact he ▸ hz
  · intro h
    exact ⟨y,h,rfl⟩

private theorem wordPath_converse {i : Interpretation} {r : OrientedRole} {x y : i.Domain} :
    holdsRole i (converse r) x y ↔ holdsRole i r y x := by
  rcases r with ⟨_, _ | _⟩ <;> rfl

private theorem rule_semantics {i : Interpretation} {chains : List Chain}
    (h : modelsChains i chains) {c : Rule} (hc : c ∈ normalize chains)
    {x y : i.Domain} (hp : WordPath i (c.pattern.body c.head) x y) :
    holdsRole i c.head x y := by
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hc
    rw [shape_body] at hp
    exact h k hk x y hp
  · obtain ⟨p,hm,rfl⟩ := List.mem_map.mp hc
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hm
    change WordPath i ((shape k).flip.body (converse (k.head,false))) x y at hp
    rw [Pattern.flip_body, shape_body] at hp
    have hp' := wordPath_flip hp
    rw [flipWord_involution] at hp'
    apply wordPath_converse.mpr
    exact h k hk y x hp'

private theorem segments_sound {i : Interpretation} {body w : Word}
    (h : Segments (body.map fun r u => ∀ x y, WordPath i u x y → holdsRole i r x y) w)
    {x y : i.Domain} (hw : WordPath i w x y) : WordPath i body x y := by
  induction body generalizing w x with
  | nil => cases h; exact hw
  | cons s tail ih =>
    cases h with
    | @cons _ _ u v hu hv =>
      obtain ⟨z,ha,hb⟩ := (wordPath_append i u v x y).mp hw
      exact ⟨z,hu x z ha,ih hv hb⟩

theorem Generated.sound {rules chains r w} (h : Generated rules (normalize chains) r w)
    {i : Interpretation} (hr : modelsRoles i rules) (hc : modelsChains i chains)
    {x y : i.Domain} (hw : WordPath i w x y) : holdsRole i r x y := by
  apply h (fun r w => ∀ x y, WordPath i w x y → holdsRole i r x y) _ x y hw
  refine ⟨fun r x y => wordPath_single.mp, ?_, ?_⟩
  · intro r s w hb hl a b hp
    rcases hb with rfl | hb
    · exact hl a b hp
    · exact modelsClosure hr _ _ hb a b (hl a b hp)
  · intro c u hm hs a b hp
    exact rule_semantics hc hm (segments_sound hs hp)

def Edge (i : Interpretation) (rules : RoleTheory) (chains : List Chain)
    (r : OrientedRole) (x y : i.Domain) : Prop :=
  ∃ word, Generated rules (normalize chains) r word ∧ WordPath i word x y

theorem Edge.flip {i rules chains r x y} (h : Edge i rules chains r x y) :
    Edge i rules chains (converse r) y x := by
  obtain ⟨w,hw,hp⟩ := h
  exact ⟨flipWord w, hw.flip, wordPath_flip hp⟩

def complete (i : Interpretation) (rules : RoleTheory) (chains : List Chain) : Interpretation :=
  {i with role := fun r x y => Edge i rules chains (r,false) x y}

theorem holdsRole_complete (i : Interpretation) (rules : RoleTheory) (chains : List Chain)
    (r : OrientedRole) (x y : i.Domain) :
    holdsRole (complete i rules chains) r x y ↔ Edge i rules chains r x y := by
  rcases r with ⟨r, _ | _⟩
  · rfl
  · exact ⟨fun h => Edge.flip (r := (r,false)) h, fun h => Edge.flip (r := (r,true)) h⟩

theorem complete_extension {i : Interpretation} {rules : RoleTheory} {chains : List Chain}
    {r : String} {x y : i.Domain} (h : i.role r x y) : (complete i rules chains).role r x y :=
  ⟨[(r,false)], (generated_closed rules (normalize chains)).letter _, wordPath_single.mpr h⟩

theorem complete_roles (i : Interpretation) (rules : RoleTheory) (chains : List Chain) :
    modelsRoles (complete i rules chains) rules := by
  intro r s he x y hr
  obtain ⟨word, hw, hp⟩ := (holdsRole_complete i rules chains r x y).mp hr
  exact (holdsRole_complete i rules chains s x y).mpr
    ⟨word, (generated_closed rules (normalize chains)).lift
      (Below.step (List.mem_append_left _ he)) hw, hp⟩

private theorem explore {i rules chains body x y}
    (h : WordPath (complete i rules chains) body x y) :
    ∃ w, Segments (body.map (Generated rules (normalize chains))) w ∧ WordPath i w x y := by
  induction body generalizing x with
  | nil => exact ⟨[],.nil,h⟩
  | cons s tail ih =>
    obtain ⟨z,hz,ht⟩ := h
    obtain ⟨u,hu,hpu⟩ := (holdsRole_complete i rules chains s x z).mp hz
    obtain ⟨v,hv,hpv⟩ := ih ht
    exact ⟨u ++ v,.cons hu hv,(wordPath_append i u v x y).mpr ⟨z,hpu,hpv⟩⟩

theorem complete_chains (i : Interpretation) (rules : RoleTheory) (chains : List Chain) :
    modelsChains (complete i rules chains) chains := by
  intro c hc x y hp
  obtain ⟨word,hw,hpath⟩ := explore hp
  refine ⟨word,(generated_closed rules (normalize chains)).rule (normalize_original hc) ?_,hpath⟩
  simpa only [shape_body] using hw

theorem holds_complete_iff {i : Interpretation} {rules chains tbox root}
    (guard : ∀ r c, .some r c ∈ closure tbox root → ∀ x y,
      Edge i rules chains (r,false) x y → holds i y c → holds i x (.some r c))
    (x : i.Domain) {c : Concept} (hc : c ∈ closure tbox root) :
    holds (complete i rules chains) x c ↔ holds i x c := by
  induction c generalizing x with
  | atom | top => rfl
  | neg c ih => simp only [holds, ih x (neg_mem_closure hc)]
  | conj a b ih₁ ih₂ =>
    obtain ⟨ha,hb⟩ := conj_mem_closure hc
    simp only [holds, ih₁ x ha, ih₂ x hb]
  | some r c ih =>
    have hc' := some_mem_closure hc
    constructor
    · rintro ⟨y,hy,hh⟩
      exact guard r c hc x y hy ((ih y hc').mp hh)
    · rintro ⟨y,hy,hh⟩
      exact ⟨y,complete_extension hy,(ih y hc').mpr hh⟩

end Sabrina.RoleChains.RankedPaths
