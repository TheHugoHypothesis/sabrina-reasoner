import Sabrina.OWL2.SROIQD.Termination.WiderDataCore

/-! Exact bounded sampling for the ordered floating-point and date/time
strata. Rational intervals represent observations; the samplers respect the
different sets of representable coordinates in each stratum. -/

namespace Sabrina.OWL2.SROIQD.Termination.WiderData

open Sabrina.OWL2 Sabrina.OWL2.Datatypes Sabrina.OWL2.SROIQD
open Sabrina.OWL2.SROIQD.Termination

private def singletonBounds (q : Rat) : RatBounds :=
  ⟨some ⟨q, true⟩, some ⟨q, true⟩⟩

private theorem singletonBounds_iff (q r : Rat) : (singletonBounds q).contains r ↔ q = r := by
  change q ≤ r ∧ r ≤ q ↔ q = r
  exact ⟨fun h => Rat.le_antisymm h.1 h.2, fun h => h ▸ ⟨Rat.le_refl, Rat.le_refl⟩⟩

private def orderBounds (order : OrderFacet) (q : Rat) : RatBounds :=
  match order with
  | .minInclusive => ⟨some ⟨q, true⟩, none⟩
  | .minExclusive => ⟨some ⟨q, false⟩, none⟩
  | .maxInclusive => ⟨none, some ⟨q, true⟩⟩
  | .maxExclusive => ⟨none, some ⟨q, false⟩⟩

private def intersectFacets (bound : Facet → Option RatBounds) : List Facet → Option RatBounds
  | [] => some {}
  | f :: fs => (bound f).bind fun a => (intersectFacets bound fs).map (a.intersect ·)

private theorem intersectFacets_iff (bound : Facet → Option RatBounds) (fs : List Facet) (q : Rat) :
    (∃ b ∈ (intersectFacets bound fs).toList, b.contains q) ↔
      ∀ f ∈ fs, ∃ b ∈ (bound f).toList, b.contains q := by
  induction fs with
  | nil => simp [intersectFacets, RatBounds.contains]
  | cons f fs ih =>
    rw [List.forall_mem_cons, ← ih]
    cases he : bound f <;> cases ht : intersectFacets bound fs <;>
      simp [intersectFacets, he, ht, RatBounds.contains_intersect]

private def axisAtom (named : IRI → Bool) (bound : Facet → Option RatBounds)
    (project : Value → Option Rat) : DataRange → List RatBounds
  | .datatype t => if t == literalDatatype || named t then [{}] else []
  | .restriction t fs => if named t then (intersectFacets bound fs).toList else []
  | .oneOf ls => ((decodeLiteralsList ls).getD []).filterMap fun v =>
      (project v).map singletonBounds
  | _ => []

private theorem axisAtom_iff (named : IRI → Bool) (bound : Facet → Option RatBounds)
    (project : Value → Option Rat) (q : Rat) (v : Value)
    (hnamed : ∀ t, checkValue t v = named t)
    (hbound : ∀ t, named t = true → ∀ f,
      ((match decodeLiteral f.bound with
        | some x => checkFacet t f.name x v
        | none => false) = true) ↔ (∃ b ∈ (bound f).toList, b.contains q))
    (hproject : ∀ w, project w = some q ↔ w = v) (a : DataRange) :
    (∃ b ∈ axisAtom named bound project a, b.contains q) ↔ evalWiderAtom a v = true := by
  cases a with
  | datatype t =>
    by_cases ht : t = literalDatatype
    · simp [ht, axisAtom, RatBounds.contains, evalWiderAtom]
    · cases he : named t <;> simp [axisAtom, ht, evalWiderAtom, hnamed, he, RatBounds.contains]
  | restriction t fs =>
    cases h : named t
    · simp [axisAtom, evalWiderAtom, hnamed, h]
    · simp only [axisAtom, h, ↓reduceIte, evalWiderAtom, hnamed, Bool.true_and,
        List.all_eq_true, intersectFacets_iff]
      exact forall_congr' fun f => imp_congr_right fun _ => (hbound t h f).symm
  | oneOf ls =>
    cases hv : decodeLiteralsList ls with
    | none => simp [axisAtom, evalWiderAtom, hv]
    | some ws =>
      simp only [axisAtom, evalWiderAtom, hv, Option.getD_some,
        List.mem_filterMap, List.contains_iff_mem]
      constructor
      · rintro ⟨b, ⟨w, hw, hb⟩, hc⟩
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hb
        have he := (singletonBounds_iff r q).mp hc
        exact (hproject w).mp (he ▸ hr) ▸ hw
      · intro hm
        exact ⟨singletonBounds q, ⟨v, hm, by rw [(hproject v).mpr rfl]; rfl⟩,
          (singletonBounds_iff q q).mpr rfl⟩
  | complement _ | union _ _ | intersection _ _ => simp [axisAtom, evalWiderAtom]

private def positiveAxis (atom : DataRange → List RatBounds) : List DataRange → List RatBounds
  | [] => [{}]
  | a :: rest => (atom a).flatMap fun b => (positiveAxis atom rest).map (b.intersect ·)

private theorem positiveAxis_iff (atom : DataRange → List RatBounds) (as : List DataRange) (q : Rat) :
    (∃ b ∈ positiveAxis atom as, b.contains q) ↔
      ∀ a ∈ as, ∃ b ∈ atom a, b.contains q := by
  induction as with
  | nil => simp [positiveAxis, RatBounds.contains]
  | cons a as ih =>
    simp only [positiveAxis, List.mem_flatMap, List.mem_map, List.forall_mem_cons]
    constructor
    · rintro ⟨b, ⟨first, hf, rest, hr, rfl⟩, hq⟩
      obtain ⟨h₁, h₂⟩ := (RatBounds.contains_intersect _ _ _).mp hq
      exact ⟨⟨first, hf, h₁⟩, ih.mp ⟨rest, hr, h₂⟩⟩
    · rintro ⟨⟨first, hf, h₁⟩, hrest⟩
      obtain ⟨rest, hr, h₂⟩ := ih.mpr hrest
      exact ⟨_, ⟨first, hf, rest, hr, rfl⟩, (RatBounds.contains_intersect _ _ _).mpr ⟨h₁, h₂⟩⟩

private def axisCell (atom : DataRange → List RatBounds) (pos neg : List DataRange) : List RatBounds :=
  foldSubtractRatBounds (positiveAxis atom pos) (neg.flatMap atom)

private theorem axisCell_iff (atom : DataRange → List RatBounds) (pos neg : List DataRange)
    (q : Rat) (v : Value)
    (ha : ∀ a, (∃ b ∈ atom a, b.contains q) ↔ evalWiderAtom a v = true) :
    (∃ b ∈ axisCell atom pos neg, b.contains q) ↔ evalWiderPartition pos neg v = true := by
  rw [axisCell, mem_foldSubtractRatBounds_iff, positiveAxis_iff]
  simp only [evalWiderPartition, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  refine and_congr (forall_congr' fun a => imp_congr_right fun _ => ha a) ?_
  constructor
  · intro h a hmem
    apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨b, hb, hq⟩ := (ha a).mpr he
    exact h b (List.mem_flatMap.mpr ⟨a, hmem, hb⟩) hq
  · intro h b hb hq
    obtain ⟨a, hmem, hba⟩ := List.mem_flatMap.mp hb
    have he := (ha a).mp ⟨b, hba, hq⟩
    rw [h a hmem] at he
    cases he

private def floatName : FloatFormat → IRI
  | .binary32 => xsd "float"
  | .binary64 => xsd "double"

private def packFloat : FloatFormat → FloatVal → Value
  | .binary32 => .float
  | .binary64 => .double

private def unpackFloat : FloatFormat → Value → Option FloatVal
  | .binary32, .float v | .binary64, .double v => some v
  | _, _ => none

private theorem packFloat_inj (f : FloatFormat) {v w : FloatVal}
    (h : packFloat f v = packFloat f w) : v = w := by
  cases f
  · exact Value.float.inj h
  · exact Value.double.inj h

private theorem checkValue_packFloat {format : FloatFormat} {v : FloatVal} (hv : format.contains v)
    (t : IRI) : checkValue t (packFloat format v) = (t == floatName format) := by
  apply Bool.eq_iff_iff.mpr
  cases format <;> simp [packFloat, floatName, checkValue_iff, valueSpace_float_iff,
    valueSpace_double_iff, hv]

private def finiteFloatFacet (f : OrderFacet) : FloatVal → Option RatBounds
  | .finite q => some (orderBounds f q)
  | .negZero | .posZero => some (orderBounds f 0)
  | .nan => none
  | .negInf => match f with
    | .minInclusive | .minExclusive => some {}
    | _ => none
  | .posInf => match f with
    | .maxInclusive | .maxExclusive => some {}
    | _ => none

private theorem finiteFloatFacet_iff (f : OrderFacet) (b : FloatVal) (q : Rat) :
    (∃ i ∈ (finiteFloatFacet f b).toList, i.contains q) ↔
      f.holdsFloat b (.finite q) = true := by
  cases b <;> cases f <;>
    simp [finiteFloatFacet, orderBounds, RatBounds.contains, RatEndpoint.holdsLower,
      RatEndpoint.holdsUpper, OrderFacet.holdsFloat, FloatVal.le, FloatVal.lt]

private def floatFacet (format : FloatFormat) (f : Facet) : Option RatBounds := do
  let order ← orderFacet f.name
  let value ← decodeLiteral f.bound
  let b ← unpackFloat format value
  finiteFloatFacet order b

private def floatProject (format : FloatFormat) (v : Value) : Option Rat := do
  let f ← unpackFloat format v
  match f with
  | .finite q => some q
  | _ => none

private theorem floatProject_iff (format : FloatFormat) (v : Value) (q : Rat) :
    floatProject format v = some q ↔ v = packFloat format (.finite q) := by
  cases format <;> cases v <;> try exact ⟨fun h => by cases h, fun h => by cases h⟩
  all_goals rename_i f; cases f <;> simp [floatProject, unpackFloat, packFloat]

private theorem floatFacet_iff (format : FloatFormat) (q : Rat) (h : format.contains (.finite q))
    (f : Facet) :
    ((match decodeLiteral f.bound with
      | some x => checkFacet (floatName format) f.name x (packFloat format (.finite q))
      | none => false) = true) ↔
      ∃ i ∈ (floatFacet format f).toList, i.contains q := by
  cases hb : decodeLiteral f.bound with
  | none => cases ho : orderFacet f.name <;> simp [floatFacet, ho, hb]
  | some v =>
    cases ho : orderFacet f.name with
    | none => cases format <;> cases v <;> simp [floatFacet, ho, hb, packFloat, checkFacet]
    | some order =>
      have chk := checkValue_packFloat h (floatName format)
      have hv : checkValue (floatName format) (packFloat format (.finite q)) = true := by
        simpa using chk
      cases format <;> cases v <;>
        simp [floatFacet, ho, hb, floatName, packFloat, unpackFloat, checkFacet,
          hv] at *
      all_goals simpa using (finiteFloatFacet_iff order _ q).symm

private def floatAxis (format : FloatFormat) :
    DataRange → List RatBounds :=
  axisAtom (· == floatName format) (floatFacet format) (floatProject format)

private theorem floatAxis_iff (format : FloatFormat) (q : Rat)
    (h : format.contains (.finite q)) (a : DataRange) :
    (∃ b ∈ floatAxis format a, b.contains q) ↔
      evalWiderAtom a (packFloat format (.finite q)) = true := by
  refine axisAtom_iff _ _ _ _ _ (checkValue_packFloat h) ?_ (fun w => floatProject_iff _ w _) a
  intro t ht f
  cases beq_iff_eq.mp ht
  exact floatFacet_iff format q h f

private def dateNamed (offset : Option Int) (t : IRI) : Bool :=
  t == xsd "dateTime" || (t == xsd "dateTimeStamp" && offset.isSome)

private theorem checkValue_packDate (q : Rat) (offset : Option Int)
    (hv : (⟨q, offset⟩ : DateTimeVal).valid) (t : IRI) :
    checkValue t (.dateTime ⟨q, offset⟩) = dateNamed offset t := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkValue_iff, valueSpace_dateTime_iff, hv, true_and,
    dateNamed, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, DateTimeVal.hasTimezone]

private def dateOrderBounds (order : OrderFacet) (b : DateTimeVal) (offset : Option Int) : RatBounds :=
  if b.hasTimezone == offset.isSome then orderBounds order b.epochSeconds
  else match order with
    | .minInclusive | .minExclusive => orderBounds .minExclusive (b.epochSeconds + 50400)
    | .maxInclusive | .maxExclusive => orderBounds .maxExclusive (b.epochSeconds - 50400)

private theorem dateOrderBounds_iff (f : OrderFacet) (b : DateTimeVal) (offset : Option Int) (q : Rat) :
    (dateOrderBounds f b offset).contains q ↔ f.holdsDateTime b ⟨q, offset⟩ = true := by
  rcases b with ⟨b, ob⟩
  cases ob <;> cases offset <;> cases f <;>
    simp [dateOrderBounds, orderBounds, RatBounds.contains, RatEndpoint.holdsLower,
      RatEndpoint.holdsUpper, DateTimeVal.hasTimezone, OrderFacet.holdsDateTime,
      DateTimeVal.le, DateTimeVal.lt, Rat.lt_sub_right_iff_add_lt]

private def dateFacet (offset : Option Int) (f : Facet) : Option RatBounds :=
  match orderFacet f.name, decodeLiteral f.bound with
  | some order, some (.dateTime b) => some (dateOrderBounds order b offset)
  | _, _ => none

private def dateProject (offset : Option Int) : Value → Option Rat
  | .dateTime dt => if dt.timezoneOffset == offset then some dt.epochSeconds else none
  | _ => none

private theorem dateProject_iff (offset : Option Int) (w : Value) (q : Rat) :
    dateProject offset w = some q ↔ w = .dateTime ⟨q, offset⟩ := by
  cases w <;> try simp [dateProject]
  rename_i dt
  rcases dt with ⟨s, o⟩
  by_cases he : o = offset <;> simp [he]

private theorem dateFacet_iff (offset : Option Int) (q : Rat) (t : IRI)
    (h : checkValue t (.dateTime ⟨q, offset⟩) = true) (f : Facet) :
    ((match decodeLiteral f.bound with
      | some x => checkFacet t f.name x (.dateTime ⟨q, offset⟩)
      | none => false) = true) ↔
      ∃ b ∈ (dateFacet offset f).toList, b.contains q := by
  cases hb : decodeLiteral f.bound with
  | none => cases ho : orderFacet f.name <;> simp [dateFacet, ho, hb]
  | some v => cases v <;> cases ho : orderFacet f.name <;>
      simp [dateFacet, hb, ho, checkFacet, h, dateOrderBounds_iff]

private def dateAxis (offset : Option Int) : DataRange → List RatBounds :=
  axisAtom (dateNamed offset) (dateFacet offset) (dateProject offset)

private theorem dateAxis_iff (offset : Option Int) (q : Rat)
    (h : (⟨q, offset⟩ : DateTimeVal).valid) (a : DataRange) :
    (∃ b ∈ dateAxis offset a, b.contains q) ↔ evalWiderAtom a (.dateTime ⟨q, offset⟩) = true :=
  axisAtom_iff _ _ _ _ _ (checkValue_packDate q offset h)
    (fun t ht f => dateFacet_iff offset q t ((checkValue_packDate q offset h t).trans ht) f)
    (fun w => dateProject_iff offset w q) a

private def scaleBounds (unit : Rat) (b : RatBounds) : RatBounds :=
  ⟨b.lower.map (fun e => ⟨e.val / unit, e.inclusive⟩),
    b.upper.map (fun e => ⟨e.val / unit, e.inclusive⟩)⟩

private theorem scaleBounds_iff (unit : Rat) (hu : 0 < unit) (b : RatBounds) (q : Rat) :
    (scaleBounds unit b).contains q ↔ b.contains (q * unit) := by
  have hlt₁ {x : Rat} : x / unit < q ↔ x < q * unit := Rat.div_lt_iff hu
  have hlt₂ {x : Rat} : q < x / unit ↔ q * unit < x := Rat.lt_div_iff hu
  have hle₁ {x : Rat} : x / unit ≤ q ↔ x ≤ q * unit := by
    rw [← Rat.not_lt, ← Rat.not_lt, hlt₂]
  have hle₂ {x : Rat} : q ≤ x / unit ↔ q * unit ≤ x := by
    rw [← Rat.not_lt, ← Rat.not_lt, hlt₁]
  rcases b with ⟨lo, hi⟩
  have hl : (lo.map (fun e => (⟨e.val / unit, e.inclusive⟩ : RatEndpoint))).elim True (·.holdsLower q) ↔
      lo.elim True (·.holdsLower (q * unit)) := by
    cases lo with
    | none => rfl
    | some e =>
      cases e with
      | mk v flag => cases flag <;> simp [RatEndpoint.holdsLower, hlt₁, hle₁]
  have hh : (hi.map (fun e => (⟨e.val / unit, e.inclusive⟩ : RatEndpoint))).elim True (·.holdsUpper q) ↔
      hi.elim True (·.holdsUpper (q * unit)) := by
    cases hi with
    | none => rfl
    | some e =>
      cases e with
      | mk v flag => cases flag <;> simp [RatEndpoint.holdsUpper, hlt₂, hle₂]
  exact and_congr hl hh

private def floatBandCell (band : FloatBand) (rs : List RatBounds) : List IntegerBounds :=
  rs.map fun r => (scaleBounds band.unit r).toIntBounds.intersect ⟨some band.lo, some band.hi⟩

private theorem floatBandCell_iff (band : FloatBand) (rs : List RatBounds) (z : Int) :
    (∃ b ∈ floatBandCell band rs, b.contains z) ↔
      (∃ r ∈ rs, r.contains (band.value z)) ∧ band.lo ≤ z ∧ z ≤ band.hi := by
  have hh (r : RatBounds) :
      ((scaleBounds band.unit r).toIntBounds.intersect ⟨some band.lo, some band.hi⟩).contains z ↔
      r.contains (band.value z) ∧ band.lo ≤ z ∧ z ≤ band.hi :=
    (IntegerBounds.contains_intersect ..).trans
      (and_congr ((RatBounds.toIntBounds_iff ..).trans (scaleBounds_iff _ band.unit_pos _ _)) Iff.rfl)
  constructor
  · rintro ⟨b, hb, hz⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    obtain ⟨hq, hs⟩ := (hh r).mp hz
    exact ⟨⟨r, hr, hq⟩, hs⟩
  · rintro ⟨⟨r, hr, hq⟩, hlo, hhi⟩
    exact ⟨_, List.mem_map_of_mem hr, (hh r).mpr ⟨hq, hlo, hhi⟩⟩

private def floatBandSamples (format : FloatFormat) (K : Nat) (rs : List RatBounds)
    (band : FloatBand) : List Value :=
  (sampleIntSet K (floatBandCell band rs)).map fun z => packFloat format (.finite (band.value z))

private def floatSpecials (format : FloatFormat) : List Value :=
  [.negInf, .posInf, .negZero, .posZero, .nan].map (packFloat format)

private theorem coverFiber {K : Nat} {pos neg : List DataRange} {xs out : List Value}
    (hnd : xs.Nodup) (hsub : ∀ v ∈ xs, v ∈ out)
    (heval : ∀ v ∈ xs, evalWiderPartition pos neg v = true)
    (hshort : (out.eraseDups.filter (evalWiderPartition pos neg)).length < K) :
    xs.length < K := by
  have hle := w_filter_length_le_of_sub_eraseDups xs out (evalWiderPartition pos neg) hnd hsub
  rw [List.filter_eq_self.mpr heval] at hle
  exact Nat.lt_of_le_of_lt hle hshort

/-- Stop as soon as one piece supplies the entire cap. -/
private def collectSamples (K : Nat) (samples : α → List Value) : List α → List Value
  | [] => []
  | a :: rest =>
    let xs := (samples a).eraseDups
    if K ≤ xs.length then xs else xs ++ collectSamples K samples rest

private theorem collectSamples_covers {α : Type} {K : Nat} {samples : α → List Value}
    {as : List α} {pos neg : List DataRange}
    (hpass : ∀ a ∈ as, ∀ v ∈ samples a, evalWiderPartition pos neg v = true)
    (hshort : ((collectSamples K samples as).eraseDups.filter
      (evalWiderPartition pos neg)).length < K) :
    ∀ a ∈ as, ∀ v ∈ samples a, v ∈ collectSamples K samples as := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [collectSamples] at hshort ⊢
    split at hshort <;> rename_i hcap
    · have hlt := coverFiber (xs := (samples a).eraseDups)
        (nodup_eraseDups_list _) (fun _ h => h)
        (fun v hv => hpass a (List.mem_cons_self ..) v (List.mem_eraseDups.mp hv)) hshort
      omega
    · have hlen := w_filter_length_le_of_sub_eraseDups
        (collectSamples K samples as).eraseDups
        ((samples a).eraseDups ++ collectSamples K samples as) (evalWiderPartition pos neg)
        (nodup_eraseDups_list _) (fun _ hv => List.mem_append_right _ (List.mem_eraseDups.mp hv))
      intro b hb v hv
      rw [ite_eq_right hcap]
      rcases List.mem_cons.mp hb with rfl | hb
      · exact List.mem_append_left _ (List.mem_eraseDups.mpr hv)
      · exact List.mem_append_right _ (ih
          (fun c hc => hpass c (List.mem_cons_of_mem _ hc))
          (Nat.lt_of_le_of_lt hlen hshort) b hb v hv)

private theorem floatBandSamples_pass (format : FloatFormat) (K : Nat) (pos neg : List DataRange)
    (band : FloatBand) (hb : band ∈ format.bands) (v : Value)
    (hv : v ∈ floatBandSamples format K (axisCell (floatAxis format) pos neg) band) :
    evalWiderPartition pos neg v = true := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
  obtain ⟨hex, hl, hu⟩ := (floatBandCell_iff _ _ _).mp (sampleIntSet_sound K _ hk)
  have hgrid := (FloatFormat.contains_finite_iff format _).mpr ⟨band, hb, k, hl, hu, rfl⟩
  exact (axisCell_iff _ pos neg _ _ (floatAxis_iff format _ hgrid)).mp hex

/-- Sample exponent bands with integer interval arithmetic. Special values
are individually tested by the final partition filter. -/
def orderedFloatCandidates (format : FloatFormat) (K : Nat) (pos neg : List DataRange) : List Value :=
  let rs := axisCell (floatAxis format) pos neg
  floatSpecials format ++ (if rs.isEmpty then []
    else collectSamples K (floatBandSamples format K rs) format.bands)

theorem orderedFloatCandidates_cover (format : FloatFormat) {K : Nat} {pos neg : List DataRange}
    {f : FloatVal} (hvalid : format.contains f)
    (hev : evalWiderPartition pos neg (packFloat format f) = true)
    (hshort : ((orderedFloatCandidates format K pos neg).eraseDups.filter
      (evalWiderPartition pos neg)).length < K) :
    packFloat format f ∈ orderedFloatCandidates format K pos neg := by
  cases f <;> try solve | simp [orderedFloatCandidates, floatSpecials]
  rename_i q
  let rs := axisCell (floatAxis format) pos neg
  obtain ⟨r, hr, hq⟩ := (axisCell_iff _ pos neg q _ (floatAxis_iff format q hvalid)).mpr hev
  have hn : rs.isEmpty = false := List.isEmpty_eq_false_iff_exists_mem.mpr ⟨r, hr⟩
  obtain ⟨band, hb, z, hlo, hhi, he⟩ := (FloatFormat.contains_finite_iff _ _).mp hvalid
  have hplus : ∀ v ∈ collectSamples K (floatBandSamples format K rs) format.bands,
      v ∈ orderedFloatCandidates format K pos neg := by
    intro v hv
    exact List.mem_append_right _ (by
      change v ∈ (if rs.isEmpty then [] else collectSamples K (floatBandSamples format K rs) format.bands)
      simp only [hn, Bool.false_eq_true, ↓reduceIte]
      exact hv)
  have hle := w_filter_length_le_of_sub_eraseDups
    (collectSamples K (floatBandSamples format K rs) format.bands).eraseDups
    (orderedFloatCandidates format K pos neg) (evalWiderPartition pos neg) (nodup_eraseDups_list _)
    (fun v hv => hplus v (List.mem_eraseDups.mp hv))
  have hsub := fun v hv => hplus v
    (collectSamples_covers
      (fun b hb v hv => floatBandSamples_pass format K pos neg b hb v hv)
      (Nat.lt_of_le_of_lt hle hshort) band hb v hv)
  have hnd : (floatBandSamples format K rs band).Nodup :=
    w_nodup_map_inj (fun h => band.value_injective (FloatVal.finite.inj (packFloat_inj format h)))
      (sampleIntSet_nodup K _)
  have hlen := coverFiber hnd hsub (floatBandSamples_pass format K pos neg band hb) hshort
  simp only [floatBandSamples, List.length_map] at hlen
  have hz := sampleIntSet_complete_of_lt K _ hlen
    ((floatBandCell_iff band rs z).mpr ⟨⟨r, hr, he ▸ hq⟩, hlo, hhi⟩)
  exact hsub _ (List.mem_map.mpr ⟨z, hz, by rw [he]⟩)

private def dateIntSamples (offset : Option Int) (K : Nat) (rs : List RatBounds) : List Value :=
  (sampleIntSet K (rs.map RatBounds.toIntBounds)).map fun z => .dateTime ⟨Rat.ofInt z, offset⟩

private def dateDecSamples (offset : Option Int) (K : Nat) (rs : List RatBounds) : List Value :=
  (sampleProperDecSet K rs).map fun q => .dateTime ⟨q, offset⟩

private def dateOffsetSamples (K : Nat) (pos neg : List DataRange) (offset : Option Int) : List Value :=
  let rs := axisCell (dateAxis offset) pos neg
  dateIntSamples offset K rs ++ dateDecSamples offset K rs

private theorem dateOffsetSamples_pass (K : Nat) (pos neg : List DataRange)
    (offset : Option Int) (ho : offset ∈ dateTimeOffsets) (v : Value)
    (hv : v ∈ dateOffsetSamples K pos neg offset) :
    evalWiderPartition pos neg v = true := by
  let rs := axisCell (dateAxis offset) pos neg
  have hpasses (u : Rat) (hdu : DecimalValue u) (hu : ∃ r ∈ rs, r.contains u) :
      evalWiderPartition pos neg (.dateTime ⟨u, offset⟩) = true :=
    (axisCell_iff _ pos neg u _
      (dateAxis_iff offset u ⟨hdu, (mem_dateTimeOffsets_iff offset).mp ho⟩)).mp hu
  rcases List.mem_append.mp hv with hi | hd
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hi
    obtain ⟨b, hb, hz⟩ := sampleIntSet_sound K _ hz
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    exact hpasses _ (decimalValue_ofInt z) ⟨r, hr, (RatBounds.toIntBounds_iff r z).mp hz⟩
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hd
    obtain ⟨he, hdec, _⟩ := sampleProperDecSet_sound K _ hu
    exact hpasses _ hdec he

def orderedDateCandidates (K : Nat) (pos neg : List DataRange) : List Value :=
  collectSamples K (dateOffsetSamples K pos neg) dateTimeOffsets

theorem orderedDateCandidates_cover {K : Nat} {pos neg : List DataRange}
    {dt : DateTimeVal} (hvalid : dt.valid)
    (hev : evalWiderPartition pos neg (.dateTime dt) = true)
    (hshort : ((orderedDateCandidates K pos neg).eraseDups.filter
      (evalWiderPartition pos neg)).length < K) :
    .dateTime dt ∈ orderedDateCandidates K pos neg := by
  rcases dt with ⟨q, offset⟩
  let rs := axisCell (dateAxis offset) pos neg
  have hex := (axisCell_iff _ pos neg q _ (dateAxis_iff offset q hvalid)).mpr hev
  have ho := (mem_dateTimeOffsets_iff offset).mpr hvalid.2
  have hsub {v} (hv : v ∈ dateIntSamples offset K rs ++ dateDecSamples offset K rs) :
      v ∈ orderedDateCandidates K pos neg :=
    collectSamples_covers (dateOffsetSamples_pass K pos neg) hshort offset ho v hv
  by_cases hd : q.den = 1
  · have hrepr : Rat.ofInt q.num = q := Rat.ext rfl hd.symm
    have hnd : (dateIntSamples offset K rs).Nodup := by
      refine w_nodup_map_inj (fun h => ?_) (sampleIntSet_nodup K _)
      exact congrArg (fun x => x.epochSeconds.num) (Value.dateTime.inj h)
    have hlen := coverFiber hnd (fun _ h => hsub (List.mem_append_left _ h))
      (fun v hv => dateOffsetSamples_pass K pos neg offset ho v (List.mem_append_left _ hv)) hshort
    simp only [dateIntSamples, List.length_map] at hlen
    obtain ⟨r, hr, hq⟩ := hex
    have hz := sampleIntSet_complete_of_lt K _ hlen
      ⟨r.toIntBounds, List.mem_map_of_mem hr, (RatBounds.toIntBounds_iff r _).mpr (hrepr ▸ hq)⟩
    exact hsub (List.mem_append_left _ (List.mem_map.mpr ⟨q.num, hz, by rw [hrepr]⟩))
  · have hnd : (dateDecSamples offset K rs).Nodup := by
      refine w_nodup_map_inj (fun h => ?_) (sampleProperDecSet_nodup K _)
      exact congrArg DateTimeVal.epochSeconds (Value.dateTime.inj h)
    have hlen := coverFiber hnd (fun _ h => hsub (List.mem_append_right _ h))
      (fun v hv => dateOffsetSamples_pass K pos neg offset ho v (List.mem_append_right _ hv)) hshort
    simp only [dateDecSamples, List.length_map] at hlen
    have hq := sampleProperDecSet_complete_of_lt K rs hlen hex hvalid.1 hd
    exact hsub (List.mem_append_right _ (List.mem_map_of_mem hq))

#print axioms orderedFloatCandidates_cover
#print axioms orderedDateCandidates_cover

end Sabrina.OWL2.SROIQD.Termination.WiderData
