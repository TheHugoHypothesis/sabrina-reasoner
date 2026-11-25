import Sabrina.RoleChains.RankedPaths

namespace Sabrina.RoleChains.RankedPaths

open Sabrina.ALC
open TransitivePaths (Below)
open PathRegex (Matches Segments)

private instance (rules : RoleTheory) (r s : OrientedRole) : Decidable (Below rules r s) :=
  inferInstanceAs (Decidable (r = s ∨ (r,s) ∈ roleClosure rules))

private def Same (rules : RoleTheory) (r s : OrientedRole) : Prop :=
  Below rules r s ∧ Below rules s r

private instance (rules : RoleTheory) (r s : OrientedRole) : Decidable (Same rules r s) :=
  inferInstanceAs (Decidable (Below rules r s ∧ Below rules s r))

private def distinct : List OrientedRole → List OrientedRole
  | [] => []
  | a :: as => (distinct as).insert a

private theorem mem_distinct {a : OrientedRole} {as : List OrientedRole} :
    a ∈ distinct as ↔ a ∈ as := by
  induction as with
  | nil => rfl
  | cons b bs ih => simp [distinct, ih]

private theorem distinct_nodup (as : List OrientedRole) : (distinct as).Nodup := by
  induction as with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    rw [distinct, List.insert]
    split
    · exact ih
    · rename_i h
      exact List.nodup_cons.mpr ⟨by simpa using h, ih⟩

private def down (rules : RoleTheory) (r : OrientedRole) : List OrientedRole :=
  distinct (ALCH.subroles (roleClosure rules) r)

private theorem mem_down {rules r s} : s ∈ down rules r ↔ Below rules s r :=
  mem_distinct.trans ALCH.mem_subroles

private def level (rank : Rank) (rules : RoleTheory) (r : OrientedRole) : Nat × Nat :=
  (rank r.1, (down rules r).length)

private def Smaller (rank : Rank) (rules : RoleTheory) (s r : OrientedRole) : Prop :=
  rank s.1 < rank r.1 ∨
    (rank s.1 = rank r.1 ∧ (down rules s).length < (down rules r).length)

private instance (rank : Rank) (rules : RoleTheory) (s r : OrientedRole) :
    Decidable (Smaller rank rules s r) :=
  inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

private theorem smaller_level {rank rules s r} (h : Smaller rank rules s r) :
    Prod.Lex (· < ·) (· < ·) (level rank rules s) (level rank rules r) := by
  rcases h with h | ⟨h, hk⟩
  · exact Prod.Lex.left _ _ h
  · unfold level
    rw [h]
    exact Prod.Lex.right _ hk

private theorem rank_le {rank rules chains} (h : Ranked rank rules chains)
    {s r} (hs : Below rules s r) : rank s.1 ≤ rank r.1 :=
  hs.elim (fun h => h ▸ Nat.le_refl _) h.respectsClosure

private theorem down_subset {rules s r} (h : Below rules s r) :
    down rules s ⊆ down rules r :=
  fun _ hs => mem_down.mpr ((mem_down.mp hs).trans h)

private theorem same_level {rank rules chains} (h : Ranked rank rules chains)
    {s r} (hs : Same rules s r) : level rank rules s = level rank rules r := by
  unfold level
  congr 1
  · exact Nat.le_antisymm (rank_le h hs.1) (rank_le h hs.2)
  · exact Nat.le_antisymm
      ((distinct_nodup _).length_le_of_subset (down_subset hs.1))
      ((distinct_nodup _).length_le_of_subset (down_subset hs.2))

private theorem smaller_proper {rank rules chains} (h : Ranked rank rules chains)
    {s r} (hs : Below rules s r) (hn : ¬ Below rules r s) : Smaller rank rules s r := by
  have hr := rank_le h hs
  rcases Nat.lt_or_eq_of_le hr with hr | hr
  · exact Or.inl hr
  · have hnd : (r :: down rules s).Nodup :=
      List.nodup_cons.mpr ⟨fun hh => hn (mem_down.mp hh), distinct_nodup _⟩
    have hsub : r :: down rules s ⊆ down rules r := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact mem_down.mpr (Below.refl _ _)
      · exact down_subset hs ha
    exact Or.inr ⟨hr, by exact hnd.length_le_of_subset hsub⟩

private def proper (rules : RoleTheory) (r : OrientedRole) : List OrientedRole :=
  (down rules r).filter fun s => decide (¬ Below rules r s)

private theorem mem_proper {rules r s} :
    s ∈ proper rules r ↔ Below rules s r ∧ ¬ Below rules r s := by
  simp [proper, mem_down]

private def component (rules : RoleTheory) (rs : List Rule) (r : OrientedRole) : List Pattern :=
  (rs.filter fun c => decide (Same rules c.head r)).map Rule.pattern

private theorem mem_component {rules rs r p} :
    p ∈ component rules rs r ↔ ∃ c ∈ rs, Same rules c.head r ∧ c.pattern = p := by
  simp [component, and_assoc]

private def words (tag : Pattern → Option Word) (ps : List Pattern) : List Word :=
  ps.filterMap tag

private def seeds : Pattern → Option Word | .base w => some w | _ => none
private def prefixes : Pattern → Option Word | .pre w => some w | _ => none
private def suffixes : Pattern → Option Word | .post w => some w | _ => none

private def pathChoices (lookup : OrientedRole → PathRegex) (ws : List Word) : PathRegex :=
  PathRegex.choice (ws.map fun w => PathRegex.sequence (w.map lookup))

private def assemble (rules : RoleTheory) (rs : List Rule) (r : OrientedRole)
    (lookup : OrientedRole → PathRegex) : PathRegex :=
  let ps := component rules rs r
  PathRegex.block
    (.alt (PathRegex.choice ((down rules r).map .symbol))
      (.alt (PathRegex.choice ((proper rules r).map lookup)) (pathChoices lookup (words seeds ps))))
    (pathChoices lookup (words prefixes ps))
    (pathChoices lookup (words suffixes ps))
    (ps.contains .transitive)

/-- Compile one role's path language. Strictly smaller components are expanded recursively.
    Unary equivalences are handled together, so a cycle in the hierarchy needs no unfolding. -/
def compile (rank : Rank) (rules : RoleTheory) (rs : List Rule) (r : OrientedRole) : PathRegex :=
  assemble rules rs r fun s =>
    if _h : Smaller rank rules s r then compile rank rules rs s else .zero
termination_by level rank rules r
decreasing_by exact smaller_level _h

private def lower (rank : Rank) (rules : RoleTheory) (rs : List Rule) (r s : OrientedRole) :
    PathRegex :=
  if Smaller rank rules s r then compile rank rules rs s else .zero

private theorem compile_eq (rank rules rs r) :
    compile rank rules rs r = assemble rules rs r (lower rank rules rs r) := by
  rw [compile]
  rfl

private theorem lower_eq {rank rules rs r s} (h : Smaller rank rules s r) :
    lower rank rules rs r s = compile rank rules rs s := by simp [lower,h]

private theorem same_lower {rank rules chains} (h : Ranked rank rules chains)
    {rs s r} (hs : Same rules s r) : lower rank rules rs s = lower rank rules rs r := by
  have he := same_level h hs
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  change rank s.1 = rank r.1 at h₁
  change (down rules s).length = (down rules r).length at h₂
  funext t
  unfold lower
  by_cases h : Smaller rank rules t r
  · have hs : Smaller rank rules t s := by simpa [Smaller, h₁, h₂] using h
    rw [ite_eq_left hs, ite_eq_left h]
  · have hs : ¬ Smaller rank rules t s := by simpa [Smaller, h₁, h₂] using h
    rw [ite_eq_right hs, ite_eq_right h]

private theorem choice_congr {as bs : List PathRegex} (h : ∀ e, e ∈ as ↔ e ∈ bs) (w : Word) :
    (PathRegex.choice as).Matches w ↔ (PathRegex.choice bs).Matches w := by
  simp only [PathRegex.matches_choice, h]

private theorem same_compile {rank rules chains} (h : Ranked rank rules chains)
    {rs s r} (hs : Same rules s r) (w : Word) :
    (compile rank rules rs s).Matches w ↔ (compile rank rules rs r).Matches w := by
  have hd (a : OrientedRole) : a ∈ down rules s ↔ a ∈ down rules r :=
    ⟨fun h => down_subset hs.1 h, fun h => down_subset hs.2 h⟩
  have hp (a : OrientedRole) : a ∈ proper rules s ↔ a ∈ proper rules r := by
    simp only [mem_proper]
    exact ⟨fun ⟨ha,hn⟩ => ⟨ha.trans hs.1, fun h => hn (hs.1.trans h)⟩,
      fun ⟨ha,hn⟩ => ⟨ha.trans hs.2, fun h => hn (hs.2.trans h)⟩⟩
  have hc (p : Pattern) : p ∈ component rules rs s ↔ p ∈ component rules rs r := by
    simp only [mem_component]
    exact ⟨fun ⟨c,hm,⟨ha,hb⟩,he⟩ => ⟨c,hm,⟨ha.trans hs.1,hs.2.trans hb⟩,he⟩,
      fun ⟨c,hm,⟨ha,hb⟩,he⟩ => ⟨c,hm,⟨ha.trans hs.2,hs.1.trans hb⟩,he⟩⟩
  have ht : (component rules rs s).contains .transitive =
      (component rules rs r).contains .transitive := by
    apply Bool.eq_iff_iff.mpr
    simpa only [List.contains_iff_mem] using hc .transitive
  rw [compile_eq, compile_eq]
  unfold assemble
  dsimp only
  rw [same_lower h hs, ht]
  have paths (tag : Pattern → Option Word) (word : Word) :
      (pathChoices (lower rank rules rs r) (words tag (component rules rs s))).Matches word ↔
      (pathChoices (lower rank rules rs r) (words tag (component rules rs r))).Matches word := by
    apply choice_congr
    intro e
    simp only [words, List.mem_map, List.mem_filterMap, hc]
  apply PathRegex.block_congr _ (paths prefixes) (paths suffixes)
  intro word
  simp only [Matches, paths seeds]
  have dh := choice_congr (as := (down rules s).map PathRegex.symbol)
    (bs := (down rules r).map PathRegex.symbol) (fun e => by simp only [List.mem_map, hd]) word
  have ph := choice_congr (as := (proper rules s).map (lower rank rules rs r))
    (bs := (proper rules r).map (lower rank rules rs r))
    (fun e => by simp only [List.mem_map, hp]) word
  rw [dh, ph]

private theorem segments_congr {L K : OrientedRole → Language} {body : Word}
    (h : ∀ s ∈ body, ∀ w, L s w ↔ K s w) {w : Word} :
    Segments (body.map L) w ↔ Segments (body.map K) w := by
  induction body generalizing w with
  | nil => rfl
  | cons s tail ih =>
    have hh := h s (List.mem_cons_self ..)
    have ht (v : Word) := ih (w := v) (fun a ha => h a (List.mem_cons_of_mem _ ha))
    constructor
    · intro hs
      cases hs with
      | cons hu hv => exact .cons ((hh _).mp hu) ((ht _).mp hv)
    · intro hs
      cases hs with
      | cons hu hv => exact .cons ((hh _).mpr hu) ((ht _).mpr hv)

theorem segments_append {L K : List Language} {w : Word} :
    Segments (L ++ K) w ↔ ∃ u v, Segments L u ∧ Segments K v ∧ w = u ++ v := by
  induction L generalizing w with
  | nil =>
    constructor
    · intro h
      exact ⟨[],w,.nil,h,rfl⟩
    · rintro ⟨u,v,hu,hv,rfl⟩
      cases hu
      exact hv
  | cons l ls ih =>
    constructor
    · intro h
      cases h with
      | @cons _ _ a b ha hb =>
        obtain ⟨u,v,hu,hv,rfl⟩ := ih.mp hb
        exact ⟨a ++ u,v,.cons ha hu,hv,(List.append_assoc ..).symm⟩
    · rintro ⟨u,v,hu,hv,rfl⟩
      cases hu with
      | @cons _ _ a b ha hb =>
        change Segments (l :: (ls ++ K)) ((a ++ b) ++ v)
        simpa only [List.append_assoc] using Segments.cons ha (ih.mpr ⟨b,v,hb,hv,rfl⟩)

theorem segments_single {L : Language} {w : Word} : Segments [L] w ↔ L w := by
  constructor
  · intro h
    cases h with
    | cons h hs => cases hs; simpa using h
  · intro h
    simpa using Segments.cons h Segments.nil

private theorem segments_lower {rank rules chains r p} (h : Ranked rank rules chains)
    (hp : p ∈ component rules (normalize chains) r) {w : Word} :
    Segments (p.lower.map (fun s => (lower rank rules (normalize chains) r s).Matches)) w ↔
      Segments (p.lower.map fun s => (compile rank rules (normalize chains) s).Matches) w := by
  obtain ⟨c,hc,he,rfl⟩ := mem_component.mp hp
  apply segments_congr
  intro s hs w
  have hr := rank_le h he.1
  rw [lower_eq (Or.inl (Nat.lt_of_lt_of_le (normalize_lower h hc hs) hr))]

private theorem matches_paths {lookup : OrientedRole → PathRegex} {ws : List Word} {w : Word} :
    (pathChoices lookup ws).Matches w ↔
      ∃ body ∈ ws, Segments (body.map fun s => (lookup s).Matches) w := by
  simp only [pathChoices, PathRegex.matches_choice, List.mem_map]
  constructor
  · rintro ⟨e,⟨b,hb,rfl⟩,he⟩
    exact ⟨b,hb,by simpa only [PathRegex.matches_sequence, List.map_map, Function.comp_def] using he⟩
  · rintro ⟨b,hb,he⟩
    exact ⟨_,⟨b,hb,rfl⟩,by simpa only [PathRegex.matches_sequence, List.map_map, Function.comp_def]
      using he⟩

/-- A family admitting each inference on oriented words. -/
structure Closed (rules : RoleTheory) (rs : List Rule) (L : OrientedRole → Language) : Prop where
  letter (r : OrientedRole) : L r [r]
  lift {r s : OrientedRole} {w : Word} : Below rules r s → L r w → L s w
  rule {r : Rule} {w : Word} : r ∈ rs → Segments ((r.pattern.body r.head).map L) w → L r.head w

/-- The least language of words forced by the oriented rules. -/
def Generated (rules : RoleTheory) (rs : List Rule) (r : OrientedRole) (w : Word) : Prop :=
  ∀ L, Closed rules rs L → L r w

theorem generated_closed (rules : RoleTheory) (rs : List Rule) : Closed rules rs (Generated rules rs) where
  letter r L h := h.letter r
  lift he hh L h := h.lift he (hh L h)
  rule hc hs L h := by
    apply h.rule hc
    rename_i c w
    generalize c.pattern.body c.head = body at hs ⊢
    induction body generalizing w with
    | nil => cases hs; exact .nil
    | cons r tail ih =>
      cases hs with
      | cons ha hb => exact .cons (ha L h) (ih hb)

private theorem mem_words {ps : List Pattern} {w : Word} :
    (w ∈ words seeds ps ↔ .base w ∈ ps) ∧
    (w ∈ words prefixes ps ↔ .pre w ∈ ps) ∧
    (w ∈ words suffixes ps ↔ .post w ∈ ps) := by
  simp only [words,List.mem_filterMap]
  constructor
  · constructor
    · rintro ⟨p,hp,he⟩; cases p <;> simp_all [seeds]
    · intro h; exact ⟨.base w,h,rfl⟩
  · constructor
    · constructor
      · rintro ⟨p,hp,he⟩; cases p <;> simp_all [prefixes]
      · intro h; exact ⟨.pre w,h,rfl⟩
    · constructor
      · rintro ⟨p,hp,he⟩; cases p <;> simp_all [suffixes]
      · intro h; exact ⟨.post w,h,rfl⟩

private theorem compiled_letter {rank rules rs r w} (h : Below rules r w) :
    (compile rank rules rs w).Matches [r] := by
  rw [compile_eq]
  exact PathRegex.block_base (Or.inl ((PathRegex.matches_choice _ _).mpr
    ⟨.symbol r,List.mem_map_of_mem (mem_down.mpr h),rfl⟩))

private theorem compiled_lift {rank rules chains r s w} (h : Ranked rank rules chains)
    (he : Below rules r s) (hw : (compile rank rules (normalize chains) r).Matches w) :
    (compile rank rules (normalize chains) s).Matches w := by
  by_cases hs : Below rules s r
  · exact (same_compile h ⟨he,hs⟩ w).mp hw
  · rw [compile_eq]
    apply PathRegex.block_base
    right
    left
    apply (PathRegex.matches_choice _ _).mpr
    refine ⟨_,List.mem_map_of_mem (mem_proper.mpr ⟨he,hs⟩),?_⟩
    rwa [lower_eq (smaller_proper h he hs)]

private theorem compiled_rule {rank rules chains c w} (h : Ranked rank rules chains)
    (hc : c ∈ normalize chains)
    (hw : Segments ((c.pattern.body c.head).map
      fun s => (compile rank rules (normalize chains) s).Matches) w) :
    (compile rank rules (normalize chains) c.head).Matches w := by
  have hm : c.pattern ∈ component rules (normalize chains) c.head :=
    mem_component.mpr ⟨c,hc,⟨Below.refl ..,Below.refl ..⟩,rfl⟩
  have ht (word : Word) := segments_lower (w := word) h hm
  cases he : c.pattern with
  | base body =>
    rw [he] at hm ht hw
    rw [compile_eq]
    exact PathRegex.block_base (Or.inr (Or.inr (matches_paths.mpr
      ⟨body,mem_words.1.mpr hm,(ht _).mpr hw⟩)))
  | pre body =>
    rw [he, Pattern.body, List.map_append] at hw
    obtain ⟨u,v,hu,hv,rfl⟩ := segments_append.mp hw
    rw [compile_eq] at ⊢
    have hv' := segments_single.mp hv
    change (compile rank rules (normalize chains) c.head).Matches v at hv'
    rw [compile_eq] at hv'
    exact PathRegex.block_prefix (matches_paths.mpr ⟨body,mem_words.2.1.mpr (he ▸ hm),
      (he ▸ ht _).mpr hu⟩) hv'
  | post body =>
    rw [he, Pattern.body] at hw
    change Segments ([_] ++ _) w at hw
    obtain ⟨u,v,hu,hv,rfl⟩ := segments_append.mp hw
    rw [compile_eq] at ⊢
    have hu' := segments_single.mp hu
    change (compile rank rules (normalize chains) c.head).Matches u at hu'
    rw [compile_eq] at hu'
    exact PathRegex.block_suffix hu' (matches_paths.mpr ⟨body,mem_words.2.2.mpr (he ▸ hm),
      (he ▸ ht _).mpr hv⟩)
  | transitive =>
    rw [he, Pattern.body] at hw
    change Segments ([_] ++ [_]) w at hw
    obtain ⟨u,v,hu,hv,rfl⟩ := segments_append.mp hw
    have ht : (component rules (normalize chains) c.head).contains .transitive = true :=
      List.contains_iff_mem.mpr (he ▸ hm)
    have heq := compile_eq rank rules (normalize chains) c.head
    unfold assemble at heq
    simp only [ht] at heq
    rw [heq]
    exact PathRegex.block_concat (heq ▸ segments_single.mp hu) (heq ▸ segments_single.mp hv)

theorem compiled_closed {rank rules chains} (h : Ranked rank rules chains) :
    Closed rules (normalize chains) (fun r => (compile rank rules (normalize chains) r).Matches) :=
  ⟨fun r => compiled_letter (Below.refl rules r), compiled_lift h, compiled_rule h⟩

theorem segments_map {L K : OrientedRole → Language} {body : Word}
    (h : ∀ s ∈ body, ∀ w, L s w → K s w) {w : Word} (hw : Segments (body.map L) w) :
    Segments (body.map K) w := by
  induction body generalizing w with
  | nil => exact hw
  | cons s tail ih =>
    cases hw with
    | cons ha hb =>
      exact .cons (h s (List.mem_cons_self ..) _ ha)
        (ih (fun t ht => h t (List.mem_cons_of_mem _ ht)) hb)

private theorem compile_least {rank rules chains} (h : Ranked rank rules chains)
    {L : OrientedRole → Language} (hc : Closed rules (normalize chains) L)
    (r : OrientedRole) (w : Word) (hw : (compile rank rules (normalize chains) r).Matches w) :
    L r w := by
  let rs := normalize chains
  let lookup := lower rank rules rs r
  have path {p : Pattern} (hm : p ∈ component rules rs r) {u : Word}
      (hu : Segments (p.lower.map fun s => (lookup s).Matches) u) :
      Segments (p.lower.map L) u := by
    apply segments_map _ ((segments_lower h hm).mp hu)
    intro s hs v hv
    obtain ⟨c,hc',he,rfl⟩ := mem_component.mp hm
    have hs' : Smaller rank rules s r :=
      Or.inl (Nat.lt_of_lt_of_le (normalize_lower h hc' hs) (rank_le h he.1))
    exact compile_least h hc s v hv
  rw [compile_eq] at hw
  change (PathRegex.block
    (.alt (PathRegex.choice ((down rules r).map .symbol))
      (.alt (PathRegex.choice ((proper rules r).map lookup))
        (pathChoices lookup (words seeds (component rules rs r)))))
    (pathChoices lookup (words prefixes (component rules rs r)))
    (pathChoices lookup (words suffixes (component rules rs r)))
    ((component rules rs r).contains .transitive)).Matches w at hw
  apply PathRegex.block_least (L := L r) _ _ _ _ hw
  · intro u hu
    rcases hu with ha | ha | ha
    · obtain ⟨e,he,hu⟩ := (PathRegex.matches_choice _ _).mp ha
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp he
      change u = [s] at hu
      subst u
      exact hc.lift (mem_down.mp hs) (hc.letter s)
    · obtain ⟨e,he,hu⟩ := (PathRegex.matches_choice _ _).mp ha
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp he
      obtain ⟨hb, hn⟩ := mem_proper.mp hs
      have hs' := smaller_proper h hb hn
      have hv : (compile rank rules rs s).Matches u := (lower_eq hs') ▸ hu
      exact hc.lift hb (compile_least h hc s u hv)
    · obtain ⟨body,hbody,hu⟩ := matches_paths.mp ha
      have hm := mem_words.1.mp hbody
      have hl := path hm hu
      obtain ⟨c,hc',he,hp⟩ := mem_component.mp hm
      have hh : Segments ((c.pattern.body c.head).map L) u := by
        rw [hp]
        exact hl
      exact hc.lift he.1 (hc.rule hc' hh)
  · intro u v hu hv
    obtain ⟨body,hbody,hu⟩ := matches_paths.mp hu
    have hm := mem_words.2.1.mp hbody
    have hl := path hm hu
    obtain ⟨c,hc',he,hp⟩ := mem_component.mp hm
    have hh : Segments ((c.pattern.body c.head).map L) (u ++ v) := by
      rw [hp, Pattern.body, List.map_append]
      exact segments_append.mpr ⟨u,v,hl,segments_single.mpr (hc.lift he.2 hv),rfl⟩
    exact hc.lift he.1 (hc.rule hc' hh)
  · intro u v hu hv
    obtain ⟨body,hbody,hv⟩ := matches_paths.mp hv
    have hm := mem_words.2.2.mp hbody
    have hl := path hm hv
    obtain ⟨c,hc',he,hp⟩ := mem_component.mp hm
    have hh : Segments ((c.pattern.body c.head).map L) (u ++ v) := by
      rw [hp, Pattern.body]
      exact .cons (hc.lift he.2 hu) hl
    exact hc.lift he.1 (hc.rule hc' hh)
  · intro ht u v hu hv
    obtain ⟨c,hc',he,hp⟩ := mem_component.mp (List.contains_iff_mem.mp ht)
    have hh : Segments ((c.pattern.body c.head).map L) (u ++ v) := by
      rw [hp, Pattern.body]
      exact .cons (hc.lift he.2 hu) (segments_single.mpr (hc.lift he.2 hv))
    exact hc.lift he.1 (hc.rule hc' hh)
termination_by level rank rules r
decreasing_by all_goals exact smaller_level hs'

/-- The ranked compiler recognizes precisely the least language generated by
    the hierarchy and every input chain, including mirrored and recursive rules. -/
theorem compile_correct {rank rules chains} (h : Ranked rank rules chains)
    (r : OrientedRole) (w : Word) :
    (compile rank rules (normalize chains) r).Matches w ↔
      Generated rules (normalize chains) r w :=
  ⟨fun hw _ hl => compile_least h hl r w hw, fun hw => hw _ (compiled_closed h)⟩

end Sabrina.RoleChains.RankedPaths
