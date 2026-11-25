import Sabrina.OWL2.DataRanges

/-! Consistency certificates for named ground data assertions, data property
ranges and functionality. Premise indices refer to the submitted axiom order. -/

namespace Sabrina.OWL2.DataCertificates

open Datatypes

structure Edge where
  role : IRI
  subject : IRI
  value : Value
  deriving DecidableEq, Repr

structure ClassFact where
  cls : IRI
  subject : IRI
  deriving DecidableEq, Repr

inductive Certificate where
  | model (edges : List Edge) (classFacts : List ClassFact := [])
  | functionalClash (functionality first second : Nat)
  | rangeClash (range assertion : Nat)
  | assertionClash (positive negative : Nat)
  | emptyRangeClash (assertion : Nat) (lower upper : Int)
  | existentialRangeClash (existential range : Nat) (lower upper : Int)
  | functionalExistentialClash (functionality existential assertion : Nat)
  | negativeExistentialClash (existential : Nat) (negatives : List Nat) (lower upper : Int)
  | subclassEmptyRangeClash (subclass membership : Nat) (lower upper : Int)
  | emptySolvedRangeClash (assertion : Nat)
  | existentialSolvedRangeClash (existential range : Nat)
  | dataMaxClash (maxIdx : Nat) (assertions : List Nat)
  | dataMinFiniteClash (minIdx : Nat)
  | keyClash (keyIdx diffIdx memA memB : Nat) (pairs : List (Nat × Nat))
  deriving DecidableEq, Repr

def Claim (o : Ontology) : Certificate → Prop
  | .model _ _ => Satisfiable datatypeMap o
  | _ => ¬ Satisfiable datatypeMap o

private abbrev IsOrdinaryRole (r : IRI) := r ≠ topDataProperty ∧ r ≠ bottomDataProperty

private abbrev OrdinaryRole := {r : IRI // IsOrdinaryRole r}

private abbrev IsOrdinaryClass (c : IRI) := c ≠ thing ∧ c ≠ nothing

private abbrev OrdinaryClass := {c : IRI // IsOrdinaryClass c}

private inductive Clause where
  | positive (r : OrdinaryRole) (a : IRI) (v : Value)
  | negative (r : OrdinaryRole) (a : IRI) (v : Value)
  | functional (r : OrdinaryRole)
  | range (r : OrdinaryRole) (t : DataRange) (test : DataRanges.Compiled t)
      (interval : Option (DataRanges.IntInterval t))
      (solved : Option (DataRanges.SolvedRange t))
  | someRange (r : OrdinaryRole) (a : IRI) (t : DataRange)
      (solved : DataRanges.SolvedRange t)
  | dataMin (n : Nat) (r : OrdinaryRole) (a : IRI) (t : DataRange)
      (solved : DataRanges.SolvedRange t)
  | dataMax (n : Nat) (r : OrdinaryRole) (a : IRI) (t : DataRange)
      (test : DataRanges.Compiled t)
  | dataExact (n : Nat) (r : OrdinaryRole) (a : IRI) (t : DataRange)
      (solved : DataRanges.SolvedRange t)
  | classMember (c : OrdinaryClass) (a : IRI)
  | subClassSomeIntInterval (c : OrdinaryClass) (r : OrdinaryRole) (t : DataRange)
      (interval : DataRanges.IntInterval t)
  | different (inds : List IRI)
  | hasKey (c : OrdinaryClass) (dataRoles : List OrdinaryRole)
  | datatypeDef (name : IRI) (body : DataRange)

private def Clause.Holds (i : Interpretation datatypeMap) : Clause → Prop
  | .positive r a v => i.dataProperties r.val (i.individuals (.named a)) (i.embedValue v)
  | .negative r a v => ¬ i.dataProperties r.val (i.individuals (.named a)) (i.embedValue v)
  | .functional r => ∀ x v w,
      i.dataProperties r.val x (i.embedValue v) → i.dataProperties r.val x (i.embedValue w) → v = w
  | .range r t _ _ _ => ∀ x y, i.dataProperties r.val x y → dataHolds i y t
  | .someRange r a t _ =>
      ∃ y, i.dataProperties r.val (i.individuals (.named a)) y ∧ dataHolds i y t
  | .dataMin n r a t _ =>
      AtLeast n (fun y => i.dataProperties r.val (i.individuals (.named a)) y ∧ dataHolds i y t)
  | .dataMax n r a t _ =>
      ¬ AtLeast (n + 1) (fun y => i.dataProperties r.val (i.individuals (.named a)) y ∧ dataHolds i y t)
  | .dataExact n r a t _ =>
      Exactly n (fun y => i.dataProperties r.val (i.individuals (.named a)) y ∧ dataHolds i y t)
  | .classMember c a => i.classes c.val (i.individuals (.named a))
  | .subClassSomeIntInterval c r t _ =>
      ∀ x, i.classes c.val x → ∃ y, i.dataProperties r.val x y ∧ dataHolds i y t
  | .different inds => inds.Pairwise fun a b => i.individuals (.named a) ≠ i.individuals (.named b)
  | .hasKey c ds =>
      ∀ x y, i.classes c.val x → i.classes c.val y → i.named x → i.named y →
        (∀ r ∈ ds, ∃ z, i.dataProperties r.val x z ∧ i.dataProperties r.val y z) → x = y
  | .datatypeDef d body => ∀ y, i.datatypes d y ↔ dataHolds i y body

private def EmbeddedEdges (i : Interpretation datatypeMap) : Prop :=
  ∀ (r : OrdinaryRole) x y, i.dataProperties r.val x y → ∃ v, i.embedValue v = y

private abbrev DatatypeDefs := List (IRI × DataRange)

private def DefsHold (i : Interpretation datatypeMap) (defs : DatatypeDefs) : Prop :=
  ∀ d body, defs.lookup d = some body → ∀ y, i.datatypes d y ↔ dataHolds i y body

private def expandOnce (defs : DatatypeDefs) : DataRange → DataRange
  | .datatype d => match defs.lookup d with | some body => body | none => .datatype d
  | .complement r => .complement (expandOnce defs r)
  | .intersection a b => .intersection (expandOnce defs a) (expandOnce defs b)
  | .union a b => .union (expandOnce defs a) (expandOnce defs b)
  | .oneOf ls => .oneOf ls
  | .restriction t fs => .restriction t fs

private def expandRange (defs : DatatypeDefs) : Nat → DataRange → DataRange
  | 0, r => r
  | n + 1, r => expandRange defs n (expandOnce defs r)

private def hasDefinedDatatype (defs : DatatypeDefs) : DataRange → Bool
  | .datatype d => (defs.lookup d).isSome
  | .complement r => hasDefinedDatatype defs r
  | .intersection a b => hasDefinedDatatype defs a || hasDefinedDatatype defs b
  | .union a b => hasDefinedDatatype defs a || hasDefinedDatatype defs b
  | .oneOf _ => false
  | .restriction t _ => (defs.lookup t).isSome

private theorem expandOnce_iff {i : Interpretation datatypeMap} {defs : DatatypeDefs}
    (hdefs : DefsHold i defs) : ∀ (r : DataRange) (y : i.Data),
    dataHolds i y (expandOnce defs r) ↔ dataHolds i y r
  | .datatype d, y => by
    simp only [expandOnce]
    cases h : defs.lookup d with
    | none => rfl
    | some body => exact (hdefs d body h y).symm
  | .complement r, y => not_congr (expandOnce_iff hdefs r y)
  | .intersection a b, y => and_congr (expandOnce_iff hdefs a y) (expandOnce_iff hdefs b y)
  | .union a b, y => or_congr (expandOnce_iff hdefs a y) (expandOnce_iff hdefs b y)
  | .oneOf _, _ => Iff.rfl
  | .restriction _ _, _ => Iff.rfl

private theorem expandRange_iff {i : Interpretation datatypeMap} {defs : DatatypeDefs}
    (hdefs : DefsHold i defs) : ∀ (n : Nat) (r : DataRange) (y : i.Data),
    dataHolds i y (expandRange defs n r) ↔ dataHolds i y r
  | 0, _, _ => Iff.rfl
  | n + 1, r, y => (expandRange_iff hdefs n (expandOnce defs r) y).trans (expandOnce_iff hdefs r y)

private def collectDefs : Ontology → Option DatatypeDefs
  | [] => some []
  | .datatypeDefinition d body :: rest => do
    if d = literalDatatype || supportedDatatype d then none
    else
      let tail ← collectDefs rest
      if (tail.lookup d).isSome then none
      else some ((d, body) :: tail)
  | _ :: rest => collectDefs rest

private theorem collectDefs_mem {o : Ontology} {defs : DatatypeDefs}
    (h : collectDefs o = some defs) {d : IRI} {body : DataRange}
    (hl : defs.lookup d = some body) : .datatypeDefinition d body ∈ o := by
  induction o generalizing defs with
  | nil => cases h; simp at hl
  | cons ax tail ih =>
    cases ax with
    | datatypeDefinition d' b' =>
      simp only [collectDefs] at h
      split at h
      · cases h
      · obtain ⟨rest, hrest, h2⟩ := Option.bind_eq_some_iff.mp h
        split at h2
        · cases h2
        · cases h2
          simp only [List.lookup] at hl
          split at hl
          · rename_i heq
            have hd : d = d' := beq_iff_eq.mp heq
            cases hl; subst hd
            exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih hrest hl)
    | _ => exact List.mem_cons_of_mem _ (ih h hl)

private theorem collectDefs_not_builtin {o : Ontology} {defs : DatatypeDefs}
    (h : collectDefs o = some defs) {d : IRI} {body : DataRange}
    (hl : defs.lookup d = some body) : d ≠ literalDatatype ∧ supportedDatatype d = false := by
  induction o generalizing defs with
  | nil => cases h; simp at hl
  | cons ax tail ih =>
    cases ax with
    | datatypeDefinition d' b' =>
      simp only [collectDefs] at h
      split at h
      · cases h
      · rename_i hnot
        obtain ⟨rest, hrest, h2⟩ := Option.bind_eq_some_iff.mp h
        split at h2
        · cases h2
        · cases h2
          simp only [List.lookup] at hl
          split at hl
          · rename_i heq
            have hd : d = d' := beq_iff_eq.mp heq
            subst hd
            simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hnot
            exact ⟨hnot.1, Bool.eq_false_iff.mpr hnot.2⟩
          · exact ih hrest hl
    | _ => exact ih h hl

private def expandAllDefs (defs : DatatypeDefs) : Option DatatypeDefs :=
  let expanded := defs.map fun (d, body) => (d, expandRange defs defs.length body)
  if expanded.all (fun (_, body) => !hasDefinedDatatype defs body) then some expanded
  else none

private theorem mem_of_lookup_eq_some {α β : Type} [BEq α] [LawfulBEq α]
    {xs : List (α × β)} {k : α} {v : β} (h : xs.lookup k = some v) : (k, v) ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons hd tail ih =>
    rcases hd with ⟨a, b⟩
    simp only [List.lookup] at h
    cases heq : k == a
    · simp only [heq] at h
      exact List.mem_cons_of_mem _ (ih h)
    · simp only [heq, Option.some.injEq] at h
      have hk : k = a := beq_iff_eq.mp heq
      subst hk h
      exact List.mem_cons_self ..

private theorem lookup_map_snd {α β γ : Type} [BEq α] [LawfulBEq α] (f : β → γ)
    (xs : List (α × β)) (k : α) :
    (xs.map fun (a, b) => (a, f b)).lookup k = (xs.lookup k).map f := by
  induction xs with
  | nil => rfl
  | cons hd tail ih =>
    rcases hd with ⟨a, b⟩
    simp only [List.map, List.lookup]
    cases h : k == a
    · exact ih
    · rfl

private structure CompiledAxiom (defs : DatatypeDefs) (a : Axiom) where
  clause : Clause
  forward : ∀ i, DefsHold i defs → axiomHolds i a → clause.Holds i
  backward : ∀ i, EmbeddedEdges i → DefsHold i defs → clause.Holds i → axiomHolds i a
  def_origin : ∀ d body, clause = .datatypeDef d body → a = .datatypeDefinition d body

private def namedIndividuals? : List Individual → Option (List IRI)
  | [] => some []
  | .named a :: rest => (namedIndividuals? rest).map (a :: ·)
  | .anonymous _ _ :: _ => none

private theorem namedIndividuals?_map {as : List Individual} {is : List IRI}
    (h : namedIndividuals? as = some is) : as = is.map Individual.named := by
  induction as generalizing is with
  | nil => cases h; rfl
  | cons a tail ih =>
    cases a with
    | anonymous _ _ => cases h
    | named name =>
      simp only [namedIndividuals?, Option.map_eq_some_iff] at h
      obtain ⟨rest, hrest, rfl⟩ := h
      simp [ih hrest]

private def ordinaryRoles? : List IRI → Option (List OrdinaryRole)
  | [] => some []
  | r :: rest =>
    if hr : IsOrdinaryRole r then (ordinaryRoles? rest).map (⟨r, hr⟩ :: ·)
    else none

private theorem ordinaryRoles?_map {rs : List IRI} {os : List OrdinaryRole}
    (h : ordinaryRoles? rs = some os) : rs = os.map Subtype.val := by
  induction rs generalizing os with
  | nil => cases h; rfl
  | cons r tail ih =>
    simp only [ordinaryRoles?] at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨rest, hrest, rfl⟩ := h
      simp [ih hrest]
    · cases h

private def compileAxiom (defs : DatatypeDefs) : (a : Axiom) → Option (CompiledAxiom defs a)
  | .dataAssertion r (.named a) l =>
    if hr : IsOrdinaryRole r then
      match hv : decodeLiteral l with
      | none => none
      | some v =>
        some ⟨.positive ⟨r,hr⟩ a v,
          fun i _ h => by simpa only [axiomHolds, Clause.Holds, i.lexicalAgreement l v hv] using h,
          fun i _ _ h => by simpa only [axiomHolds, Clause.Holds, i.lexicalAgreement l v hv] using h,
          fun _ _ h => by cases h⟩
    else none
  | .negativeDataAssertion r (.named a) l =>
    if hr : IsOrdinaryRole r then
      match hv : decodeLiteral l with
      | none => none
      | some v =>
        some ⟨.negative ⟨r,hr⟩ a v,
          fun i _ h => by simpa only [axiomHolds, Clause.Holds, i.lexicalAgreement l v hv] using h,
          fun i _ _ h => by simpa only [axiomHolds, Clause.Holds, i.lexicalAgreement l v hv] using h,
          fun _ _ h => by cases h⟩
    else none
  | .functionalDataProperty r =>
    if hr : IsOrdinaryRole r then
      some ⟨.functional ⟨r,hr⟩, by
        intro i _ h x v w hv hw
        exact i.embedValue_injective (h _ _ _ hv hw), by
        intro i hi _ hc x y z hy hz
        obtain ⟨v,rfl⟩ := hi ⟨r,hr⟩ x y hy
        obtain ⟨w,rfl⟩ := hi ⟨r,hr⟩ x z hz
        exact congrArg i.embedValue (hc x v w hy hz),
        fun _ _ h => by cases h⟩
    else none
  | .dataPropertyRange r t =>
    if hr : IsOrdinaryRole r then do
      let t' := expandRange defs defs.length t
      let test ← DataRanges.compile t'
      let interval := DataRanges.compileIntInterval t'
      let solved := DataRanges.compileSolvedRange t'
      return ⟨.range ⟨r,hr⟩ t' test interval solved,
        fun i hd h x y hy => (expandRange_iff hd defs.length t y).mpr (h x y hy),
        fun i _ hd h x y hy => (expandRange_iff hd defs.length t y).mp (h x y hy),
        fun _ _ h => by cases h⟩
    else none
  | .classAssertion (.dataSome r t) (.named a) =>
    if hr : IsOrdinaryRole r then do
      let t' := expandRange defs defs.length t
      let solved ← DataRanges.compileSolvedRange t'
      return ⟨.someRange ⟨r,hr⟩ a t' solved,
        fun i hd ⟨y, hy, ht⟩ => ⟨y, hy, (expandRange_iff hd defs.length t y).mpr ht⟩,
        fun i _ hd ⟨y, hy, ht⟩ => ⟨y, hy, (expandRange_iff hd defs.length t y).mp ht⟩,
        fun _ _ h => by cases h⟩
    else none
  | .classAssertion (.dataMin n r t) (.named a) =>
    if hr : IsOrdinaryRole r then do
      let t' := expandRange defs defs.length t
      let solved ← DataRanges.compileSolvedRange t'
      return ⟨.dataMin n ⟨r,hr⟩ a t' solved,
        fun i hd ⟨xs, hl, hnd, hp⟩ => ⟨xs, hl, hnd, fun y hy =>
          ⟨(hp y hy).1, (expandRange_iff hd defs.length t y).mpr (hp y hy).2⟩⟩,
        fun i _ hd ⟨xs, hl, hnd, hp⟩ => ⟨xs, hl, hnd, fun y hy =>
          ⟨(hp y hy).1, (expandRange_iff hd defs.length t y).mp (hp y hy).2⟩⟩,
        fun _ _ h => by cases h⟩
    else none
  | .classAssertion (.dataMax n r t) (.named a) =>
    if hr : IsOrdinaryRole r then do
      let t' := expandRange defs defs.length t
      let test ← DataRanges.compile t'
      return ⟨.dataMax n ⟨r,hr⟩ a t' test,
        fun i hd h ⟨xs, hl, hnd, hp⟩ => h ⟨xs, hl, hnd, fun y hy =>
          ⟨(hp y hy).1, (expandRange_iff hd defs.length t y).mp (hp y hy).2⟩⟩,
        fun i _ hd h ⟨xs, hl, hnd, hp⟩ => h ⟨xs, hl, hnd, fun y hy =>
          ⟨(hp y hy).1, (expandRange_iff hd defs.length t y).mpr (hp y hy).2⟩⟩,
        fun _ _ h => by cases h⟩
    else none
  | .classAssertion (.dataExact n r t) (.named a) =>
    if hr : IsOrdinaryRole r then do
      let t' := expandRange defs defs.length t
      let solved ← DataRanges.compileSolvedRange t'
      return ⟨.dataExact n ⟨r,hr⟩ a t' solved,
        fun i hd ⟨⟨xs, hl, hnd, hp⟩, hmax⟩ =>
          ⟨⟨xs, hl, hnd, fun y hy => ⟨(hp y hy).1, (expandRange_iff hd defs.length t y).mpr (hp y hy).2⟩⟩,
           fun ⟨xs', hl', hnd', hp'⟩ => hmax ⟨xs', hl', hnd', fun y hy =>
             ⟨(hp' y hy).1, (expandRange_iff hd defs.length t y).mp (hp' y hy).2⟩⟩⟩,
        fun i _ hd ⟨⟨xs, hl, hnd, hp⟩, hmax⟩ =>
          ⟨⟨xs, hl, hnd, fun y hy => ⟨(hp y hy).1, (expandRange_iff hd defs.length t y).mp (hp y hy).2⟩⟩,
           fun ⟨xs', hl', hnd', hp'⟩ => hmax ⟨xs', hl', hnd', fun y hy =>
             ⟨(hp' y hy).1, (expandRange_iff hd defs.length t y).mpr (hp' y hy).2⟩⟩⟩,
        fun _ _ h => by cases h⟩
    else none
  | .classAssertion (.named c) (.named a) =>
    if hc : IsOrdinaryClass c then
      some ⟨.classMember ⟨c,hc⟩ a, fun _ _ h => h, fun _ _ _ h => h, fun _ _ h => by cases h⟩
    else none
  | .subClassOf (.named c) (.dataSome r t) =>
    if hc : IsOrdinaryClass c then
      if hr : IsOrdinaryRole r then do
        let t' := expandRange defs defs.length t
        let interval ← DataRanges.compileIntInterval t'
        return ⟨.subClassSomeIntInterval ⟨c,hc⟩ ⟨r,hr⟩ t' interval,
          fun i hd h x hx =>
            let ⟨y, hy, ht⟩ := h x hx
            ⟨y, hy, (expandRange_iff hd defs.length t y).mpr ht⟩,
          fun i _ hd h x hx =>
            let ⟨y, hy, ht⟩ := h x hx
            ⟨y, hy, (expandRange_iff hd defs.length t y).mp ht⟩,
          fun _ _ h => by cases h⟩
      else none
    else none
  | .differentIndividuals as =>
    match h : namedIndividuals? as with
    | none => none
    | some is =>
      some ⟨.different is, by
        intro i _ hi
        have hm := namedIndividuals?_map h
        subst hm
        exact (List.pairwise_map (f := Individual.named)
          (R := fun a b => i.individuals a ≠ i.individuals b)).mp hi, by
        intro i _ _ hc
        have hm := namedIndividuals?_map h
        subst hm
        exact (List.pairwise_map (f := Individual.named)
          (R := fun a b => i.individuals a ≠ i.individuals b)).mpr hc,
        fun _ _ h => by cases h⟩
  | .hasKey (.named c) [] ds =>
    if hc : IsOrdinaryClass c then
      match h : ordinaryRoles? ds with
      | none => none
      | some os =>
        some ⟨.hasKey ⟨c, hc⟩ os, by
          intro i _ hi x y hx hy hnx hny hds
          have hm := ordinaryRoles?_map h
          subst hm
          exact hi x y hx hy hnx hny (by simp) (by
            intro r hr
            obtain ⟨ro, hro, rfl⟩ := List.mem_map.mp hr
            exact hds ro hro), by
          intro i _ _ hkey x y hx hy hnx hny _ hds
          have hm := ordinaryRoles?_map h
          subst hm
          exact hkey x y hx hy hnx hny (fun ro hro => hds ro.val (List.mem_map_of_mem hro)),
          fun _ _ h => by cases h⟩
    else none
  | .datatypeDefinition d body =>
    some ⟨.datatypeDef d body, fun _ _ h => h, fun _ _ _ h => h, fun _ _ h => by cases h; rfl⟩
  | _ => none

private theorem collectDefs_complete {o : Ontology} {defs : DatatypeDefs}
    (h : collectDefs o = some defs) {d : IRI} {body : DataRange}
    (hm : .datatypeDefinition d body ∈ o) : defs.lookup d = some body := by
  induction o generalizing defs with
  | nil => cases hm
  | cons ax tail ih =>
    cases ax with
    | datatypeDefinition d' b' =>
      simp only [collectDefs] at h
      split at h
      · cases h
      · obtain ⟨rest, hrest, h2⟩ := Option.bind_eq_some_iff.mp h
        split at h2
        · cases h2
        · rename_i hnot
          cases h2
          rcases List.mem_cons.mp hm with heq | hm'
          · cases heq; simp [List.lookup]
          · have hrest_lk := ih hrest hm'
            have hne : d ≠ d' := by
              intro hdd; subst hdd
              simp [hrest_lk] at hnot
            simp [List.lookup, beq_false_of_ne hne, hrest_lk]
    | _ =>
      rcases List.mem_cons.mp hm with heq | hm'
      · cases heq
      · exact ih h hm'

private structure CompiledOntology (o : Ontology) where
  defs : DatatypeDefs
  expandedDefs : DatatypeDefs
  defs_ok : ∀ d body, defs.lookup d = some body → d ≠ literalDatatype ∧ supportedDatatype d = false
  expanded_ok : expandedDefs = defs.map (fun (d, body) => (d, expandRange defs defs.length body))
  expanded_acyclic : ∀ d body, expandedDefs.lookup d = some body → hasDefinedDatatype defs body = false
  clauses : List Clause
  defs_clauses : ∀ d body, .datatypeDef d body ∈ clauses → defs.lookup d = some body
  forward : ∀ i, satisfies i o → ∀ c ∈ clauses, c.Holds i
  backward : ∀ i, EmbeddedEdges i → DefsHold i defs → (∀ c ∈ clauses, c.Holds i) → satisfies i o

private def compileAxioms (defs : DatatypeDefs) : (o : Ontology) →
    Option { cs : List Clause //
      (∀ d body, .datatypeDef d body ∈ cs → .datatypeDefinition d body ∈ o) ∧
      (∀ i, DefsHold i defs → satisfies i o → ∀ c ∈ cs, c.Holds i) ∧
      (∀ i, EmbeddedEdges i → DefsHold i defs → (∀ c ∈ cs, c.Holds i) → satisfies i o) }
  | [] => some ⟨[], by simp, by simp, by simp [satisfies]⟩
  | a :: o => do
    let head ← compileAxiom defs a
    let tail ← compileAxioms defs o
    return ⟨head.clause :: tail.val, by
      intro d body hm
      rcases List.mem_cons.mp hm with hcl | hm'
      · rw [head.def_origin d body hcl.symm]
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (tail.property.1 d body hm'), by
      intro i hd hi c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact head.forward i hd (hi a (List.mem_cons_self ..))
      · exact tail.property.2.1 i hd (fun a ha => hi a (List.mem_cons_of_mem _ ha)) c hc, by
      intro i he hd h b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact head.backward i he hd (h _ (List.mem_cons_self ..))
      · exact tail.property.2.2 i he hd (fun c hc => h c (List.mem_cons_of_mem _ hc)) b hb⟩

private def compile (o : Ontology) : Option (CompiledOntology o) :=
  match hdefs : collectDefs o with
  | none => none
  | some defs =>
    match hexp : expandAllDefs defs with
    | none => none
    | some expandedDefs =>
      match compileAxioms defs o with
      | none => none
      | some ⟨cs, hdefmem, hfwd, hbwd⟩ =>
        some ⟨defs, expandedDefs,
          fun d body hl => collectDefs_not_builtin hdefs hl,
          (by
            simp only [expandAllDefs] at hexp
            split at hexp
            · cases hexp; rfl
            · cases hexp),
          (by
            intro d body hl
            simp only [expandAllDefs] at hexp
            split at hexp
            · rename_i hall
              cases hexp
              have hmem := mem_of_lookup_eq_some hl
              have hstep := List.all_eq_true.mp hall (d, body) hmem
              simpa using hstep
            · cases hexp),
          cs,
          fun d body hm => collectDefs_complete hdefs (hdefmem d body hm),
          fun i hs => hfwd i (fun d body hl => hs _ (collectDefs_mem hdefs hl)) hs,
          hbwd⟩

/-- Base interpretation with no custom datatype definitions. -/
private def baseInterpretation (edges : List Edge) (classFacts : List ClassFact) :
    Interpretation datatypeMap where
  Object := IRI
  objectNonempty := ⟨""⟩
  Data := Option Value
  dataNonempty := ⟨none⟩
  embedValue := some
  embedValue_injective := Option.some.inj
  classes c a := c = thing ∨ (c ≠ nothing ∧ ⟨c, a⟩ ∈ classFacts)
  objectProperties r _ _ := r = topObjectProperty
  dataProperties r a y := r = topDataProperty ∨
    (r ≠ bottomDataProperty ∧ ∃ v, some v = y ∧ ⟨r,a,v⟩ ∈ edges)
  individuals
    | .named a => a
    | .anonymous _ _ => ""
  datatypes t y := t = literalDatatype ∨ ∃ v, valueSpace t v ∧ some v = y
  literalValue := decodeLiteral
  lexicalAgreement := fun _ _ h => h
  named _ := True
  namedIndividual _ := trivial
  thingExt _ := Or.inl rfl
  nothingExt _ := by
    rintro (h | ⟨h, _⟩)
    · exact (by decide : nothing ≠ thing) h
    · exact h rfl
  topObjectExt _ _ := rfl
  bottomObjectExt _ _ := by decide
  topDataExt _ _ := Or.inl rfl
  bottomDataExt _ _ := by
    rintro (h | ⟨h,_⟩)
    · exact (by decide : bottomDataProperty ≠ topDataProperty) h
    · exact h rfl
  literalDatatypeExt _ := Or.inl rfl
  datatypeAgreement t ht _ := by
    have hn : t ≠ literalDatatype := fun e => datatypeMap.literal_not_builtin (e ▸ ht)
    simp only [hn, false_or]
    rfl

/-- Keep the underlying object and data domains nonempty. Custom datatype
definitions are interpreted by evaluating their acyclic expanded bodies in the
base interpretation. -/
private def interpretation (edges : List Edge) (classFacts : List ClassFact)
    {o : Ontology} (prepared : CompiledOntology o) :
    Interpretation datatypeMap where
  Object := IRI
  objectNonempty := ⟨""⟩
  Data := Option Value
  dataNonempty := ⟨none⟩
  embedValue := some
  embedValue_injective := Option.some.inj
  classes c a := c = thing ∨ (c ≠ nothing ∧ ⟨c, a⟩ ∈ classFacts)
  objectProperties r _ _ := r = topObjectProperty
  dataProperties r a y := r = topDataProperty ∨
    (r ≠ bottomDataProperty ∧ ∃ v, some v = y ∧ ⟨r,a,v⟩ ∈ edges)
  individuals
    | .named a => a
    | .anonymous _ _ => ""
  datatypes t y :=
    match prepared.expandedDefs.lookup t with
    | some body => dataHolds (baseInterpretation edges classFacts) y body
    | none => t = literalDatatype ∨ ∃ v, valueSpace t v ∧ some v = y
  literalValue := decodeLiteral
  lexicalAgreement := fun _ _ h => h
  named _ := True
  namedIndividual _ := trivial
  thingExt _ := Or.inl rfl
  nothingExt _ := by
    rintro (h | ⟨h, _⟩)
    · exact (by decide : nothing ≠ thing) h
    · exact h rfl
  topObjectExt _ _ := rfl
  bottomObjectExt _ _ := by decide
  topDataExt _ _ := Or.inl rfl
  bottomDataExt _ _ := by
    rintro (h | ⟨h,_⟩)
    · exact (by decide : bottomDataProperty ≠ topDataProperty) h
    · exact h rfl
  literalDatatypeExt y := by
    have hnone : prepared.expandedDefs.lookup literalDatatype = none := by
      rw [prepared.expanded_ok, lookup_map_snd]
      cases h : prepared.defs.lookup literalDatatype with
      | none => rfl
      | some body => exact False.elim ((prepared.defs_ok _ _ h).1 rfl)
    simp [hnone]
  datatypeAgreement t ht y := by
    have hnone : prepared.expandedDefs.lookup t = none := by
      rw [prepared.expanded_ok, lookup_map_snd]
      cases h : prepared.defs.lookup t with
      | none => rfl
      | some body =>
        have hfalse := (prepared.defs_ok _ _ h).2
        have htrue : supportedDatatype t = true := ht
        rw [hfalse] at htrue
        cases htrue
    have hn : t ≠ literalDatatype := fun e => datatypeMap.literal_not_builtin (e ▸ ht)
    simp only [hnone, hn, false_or]
    rfl

private theorem dataHolds_interpretation_eq_base {edges : List Edge} {classFacts : List ClassFact}
    {o : Ontology} (prepared : CompiledOntology o) :
    ∀ (r : DataRange) (y : Option Value), hasDefinedDatatype prepared.defs r = false →
      (dataHolds (interpretation edges classFacts prepared) y r ↔
        dataHolds (baseInterpretation edges classFacts) y r)
  | .datatype t, y, hno => by
    have hnone : prepared.expandedDefs.lookup t = none := by
      rw [prepared.expanded_ok, lookup_map_snd]
      cases h : prepared.defs.lookup t with
      | none => rfl
      | some _ => simp [hasDefinedDatatype, h] at hno
    simp [dataHolds, interpretation, baseInterpretation, hnone]
  | .complement r, y, hno =>
    not_congr (dataHolds_interpretation_eq_base prepared r y hno)
  | .intersection a b, y, hno => by
    simp only [hasDefinedDatatype, Bool.or_eq_false_iff] at hno
    exact and_congr (dataHolds_interpretation_eq_base prepared a y hno.1)
      (dataHolds_interpretation_eq_base prepared b y hno.2)
  | .union a b, y, hno => by
    simp only [hasDefinedDatatype, Bool.or_eq_false_iff] at hno
    exact or_congr (dataHolds_interpretation_eq_base prepared a y hno.1)
      (dataHolds_interpretation_eq_base prepared b y hno.2)
  | .oneOf _, _, _ => Iff.rfl
  | .restriction t fs, y, hno => by
    have hnone : prepared.expandedDefs.lookup t = none := by
      rw [prepared.expanded_ok, lookup_map_snd]
      cases h : prepared.defs.lookup t with
      | none => rfl
      | some _ => simp [hasDefinedDatatype, h] at hno
    exact and_congr (by simp [interpretation, baseInterpretation, hnone]) Iff.rfl

private theorem expandRange_noDefined_step (defs : DatatypeDefs) (r : DataRange)
    (h : hasDefinedDatatype defs r = false) : expandOnce defs r = r := by
  induction r with
  | datatype d =>
    simp only [hasDefinedDatatype] at h
    cases hl : defs.lookup d with
    | none => simp [expandOnce, hl]
    | some _ => simp [hl] at h
  | complement r ih => simp [expandOnce, ih h]
  | intersection a b iha ihb =>
    simp only [hasDefinedDatatype, Bool.or_eq_false_iff] at h
    simp [expandOnce, iha h.1, ihb h.2]
  | union a b iha ihb =>
    simp only [hasDefinedDatatype, Bool.or_eq_false_iff] at h
    simp [expandOnce, iha h.1, ihb h.2]
  | oneOf _ => rfl
  | restriction _ _ => rfl

private theorem expandRange_fixpoint (defs : DatatypeDefs) (n : Nat) (r : DataRange)
    (h : hasDefinedDatatype defs r = false) : expandRange defs n r = r := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [expandRange, expandRange_noDefined_step defs r h]
    exact ih

private theorem expandRange_add (defs : DatatypeDefs) (a b : Nat) (r : DataRange) :
    expandRange defs (a + b) r = expandRange defs b (expandRange defs a r) := by
  induction a generalizing r with
  | zero => simp [expandRange]
  | succ k ih =>
    rw [Nat.succ_add]
    exact ih (expandOnce defs r)

private theorem expandRange_eq_of_noDefined {defs : DatatypeDefs} {k n : Nat} {r : DataRange}
    (hk : hasDefinedDatatype defs (expandRange defs k r) = false)
    (hn : hasDefinedDatatype defs (expandRange defs n r) = false) :
    expandRange defs k r = expandRange defs n r := by
  have h1 : expandRange defs (k + n) r = expandRange defs k r := by
    rw [expandRange_add, expandRange_fixpoint defs n _ hk]
  have h2 : expandRange defs (n + k) r = expandRange defs n r := by
    rw [expandRange_add, expandRange_fixpoint defs k _ hn]
  rw [Nat.add_comm] at h1
  exact h1.symm.trans h2

private theorem dataHolds_interpretation_expand_iff {edges : List Edge} {classFacts : List ClassFact}
    {o : Ontology} (prepared : CompiledOntology o) (y : Option Value) :
    ∀ (k : Nat) (r : DataRange),
      hasDefinedDatatype prepared.defs (expandRange prepared.defs k r) = false →
      (dataHolds (interpretation edges classFacts prepared) y r ↔
        dataHolds (baseInterpretation edges classFacts) y (expandRange prepared.defs k r))
  | 0, r, hno => dataHolds_interpretation_eq_base prepared r y hno
  | k + 1, r, hno => by
    induction r with
    | datatype d =>
      simp only [expandRange, expandOnce] at hno ⊢
      cases h : prepared.defs.lookup d with
      | none =>
        have hno' : hasDefinedDatatype prepared.defs (.datatype d) = false := by
          simp [hasDefinedDatatype, h]
        have hfix := expandRange_fixpoint prepared.defs k (.datatype d) hno'
        rw [hfix]
        exact dataHolds_interpretation_eq_base prepared (.datatype d) y hno'
      | some body =>
        simp only [h] at hno ⊢
        have hexp : prepared.expandedDefs.lookup d =
            some (expandRange prepared.defs prepared.defs.length body) := by
          rw [prepared.expanded_ok, lookup_map_snd, h]; rfl
        have hnoBody : hasDefinedDatatype prepared.defs
            (expandRange prepared.defs prepared.defs.length body) = false :=
          prepared.expanded_acyclic d _ hexp
        have heq := expandRange_eq_of_noDefined hnoBody hno
        simp only [dataHolds, interpretation, hexp, heq]
    | complement r ih =>
      have hcomm : ∀ (m : Nat) (x : DataRange),
          expandRange prepared.defs m (.complement x) = .complement (expandRange prepared.defs m x) := by
        intro m
        induction m with
        | zero => intro _; rfl
        | succ m ihm => intro x; exact ihm (expandOnce prepared.defs x)
      rw [hcomm (k + 1) r] at hno ⊢
      exact not_congr (ih hno)
    | intersection a b iha ihb =>
      have hcomm : ∀ (m : Nat) (x y : DataRange),
          expandRange prepared.defs m (.intersection x y) =
            .intersection (expandRange prepared.defs m x) (expandRange prepared.defs m y) := by
        intro m
        induction m with
        | zero => intro _ _; rfl
        | succ m ihm => intro x y; exact ihm (expandOnce prepared.defs x) (expandOnce prepared.defs y)
      rw [hcomm (k + 1) a b] at hno ⊢
      simp only [hasDefinedDatatype, Bool.or_eq_false_iff] at hno
      exact and_congr (iha hno.1) (ihb hno.2)
    | union a b iha ihb =>
      have hcomm : ∀ (m : Nat) (x y : DataRange),
          expandRange prepared.defs m (.union x y) =
            .union (expandRange prepared.defs m x) (expandRange prepared.defs m y) := by
        intro m
        induction m with
        | zero => intro _ _; rfl
        | succ m ihm => intro x y; exact ihm (expandOnce prepared.defs x) (expandOnce prepared.defs y)
      rw [hcomm (k + 1) a b] at hno ⊢
      simp only [hasDefinedDatatype, Bool.or_eq_false_iff] at hno
      exact or_congr (iha hno.1) (ihb hno.2)
    | oneOf ls =>
      have hcomm : ∀ m, expandRange prepared.defs m (.oneOf ls) = .oneOf ls := by
        intro m; induction m with | zero => rfl | succ m ihm => exact ihm
      rw [hcomm]
      exact Iff.rfl
    | restriction t fs =>
      have hcomm : ∀ m, expandRange prepared.defs m (.restriction t fs) = .restriction t fs := by
        intro m; induction m with | zero => rfl | succ m ihm => exact ihm
      rw [hcomm] at hno ⊢
      exact dataHolds_interpretation_eq_base prepared (.restriction t fs) y hno

private theorem defsHold_interpretation (edges : List Edge) (classFacts : List ClassFact)
    {o : Ontology} (prepared : CompiledOntology o) :
    DefsHold (interpretation edges classFacts prepared) prepared.defs := by
  intro d body h y
  have hexp : prepared.expandedDefs.lookup d =
      some (expandRange prepared.defs prepared.defs.length body) := by
    rw [prepared.expanded_ok, lookup_map_snd, h]; rfl
  have hnoBody : hasDefinedDatatype prepared.defs
      (expandRange prepared.defs prepared.defs.length body) = false :=
    prepared.expanded_acyclic d _ hexp
  have hiff := dataHolds_interpretation_expand_iff (edges := edges) (classFacts := classFacts)
    prepared y prepared.defs.length body hnoBody
  exact (by simp [interpretation, hexp] :
    (interpretation edges classFacts prepared).datatypes d y ↔
      dataHolds (baseInterpretation edges classFacts) y
        (expandRange prepared.defs prepared.defs.length body)).trans hiff.symm

private theorem embedded (edges : List Edge) (classFacts : List ClassFact)
    {o : Ontology} (prepared : CompiledOntology o) :
    EmbeddedEdges (interpretation edges classFacts prepared) := by
  intro r x y h
  rcases h with htop | ⟨_,v,hv,_⟩
  · exact False.elim (r.property.1 htop)
  · exact ⟨v,hv⟩

private theorem ordinary_edge_iff (edges : List Edge) (classFacts : List ClassFact)
    {o : Ontology} (prepared : CompiledOntology o) (r : OrdinaryRole) (a : IRI) (v : Value) :
    (interpretation edges classFacts prepared).dataProperties r.val a
      ((interpretation edges classFacts prepared).embedValue v) ↔
      (⟨r.val,a,v⟩ : Edge) ∈ edges := by
  change (r.val = topDataProperty ∨
    (r.val ≠ bottomDataProperty ∧ ∃ w, some w = some v ∧ (⟨r.val,a,w⟩ : Edge) ∈ edges)) ↔ _
  simp [r.property.1, r.property.2]

private theorem ordinary_class_iff (edges : List Edge) (classFacts : List ClassFact)
    {o : Ontology} (prepared : CompiledOntology o) (c : OrdinaryClass) (a : IRI) :
    (interpretation edges classFacts prepared).classes c.val a ↔
      (⟨c.val, a⟩ : ClassFact) ∈ classFacts := by
  change (c.val = thing ∨ (c.val ≠ nothing ∧ (⟨c.val, a⟩ : ClassFact) ∈ classFacts)) ↔ _
  simp [c.property.1, c.property.2]

private def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs =>
    let rest := dedup xs
    if x ∈ rest then rest else x :: rest

private theorem mem_dedup {α : Type} [DecidableEq α] {x : α} {xs : List α} :
    x ∈ dedup xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [dedup]
  | cons a tail ih =>
    simp only [dedup]
    split
    · rename_i ha
      constructor
      · intro hx; exact List.mem_cons_of_mem _ (ih.mp hx)
      · intro hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ha
        · exact ih.mpr hx'
    · simp [ih]

private theorem dedup_nodup {α : Type} [DecidableEq α] : ∀ (xs : List α), (dedup xs).Nodup
  | [] => List.nodup_nil
  | x :: xs => by
    simp only [dedup]
    split
    · exact dedup_nodup xs
    · rename_i hnot
      exact List.nodup_cons.mpr ⟨hnot, dedup_nodup xs⟩

private theorem nodup_map_injective {α β : Type} {f : α → β}
    (hinj : ∀ {a b}, f a = f b → a = b) {xs : List α} (h : xs.Nodup) : (xs.map f).Nodup :=
  List.pairwise_map.mpr (h.imp fun hne he => hne (hinj he))

private theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] :
    ∀ (xs ys : List α), xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hnd, hsub => by
    have hx : x ∈ ys := hsub x (List.mem_cons_self ..)
    have hnd' := List.nodup_cons.mp hnd
    have hsub' : ∀ z ∈ xs, z ∈ ys.erase x := fun z hz =>
      (List.mem_erase_of_ne (fun (he : z = x) => hnd'.1 (he ▸ hz))).mpr (hsub z (List.mem_cons_of_mem _ hz))
    have ih := length_le_of_nodup_subset xs (ys.erase x) hnd'.2 hsub'
    have hlen : (ys.erase x).length + 1 = ys.length := by
      rw [List.length_erase_of_mem hx]
      have hpos : 0 < ys.length := List.length_pos_of_mem hx
      omega
    simp only [List.length_cons]
    omega

private def matchingValues (edges : List Edge) (r : OrdinaryRole) (a : IRI)
    (test : Value → Bool) : List Value :=
  dedup ((edges.filter fun e => e.role == r.val && e.subject == a && test e.value).map (·.value))

private theorem matchingValues_sound {edges : List Edge} {classFacts : List ClassFact}
    {o : Ontology} {prepared : CompiledOntology o}
    {r : OrdinaryRole} {a : IRI} {t : DataRange} (test : DataRanges.Compiled t)
    {v : Value} (hv : v ∈ matchingValues edges r a test.holds) :
    (interpretation edges classFacts prepared).dataProperties r.val
      ((interpretation edges classFacts prepared).individuals (.named a))
      ((interpretation edges classFacts prepared).embedValue v) ∧
    dataHolds (interpretation edges classFacts prepared)
      ((interpretation edges classFacts prepared).embedValue v) t := by
  have hmem := mem_dedup.mp hv
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
  obtain ⟨he_in, hcond⟩ := List.mem_filter.mp he
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
  rcases hcond with ⟨⟨hr, ha⟩, hholds⟩
  have hedge : (⟨r.val, a, e.value⟩ : Edge) ∈ edges := by
    rcases e with ⟨er, ea, ev⟩
    subst hr ha
    exact he_in
  exact ⟨(ordinary_edge_iff edges classFacts prepared r a e.value).mpr hedge,
    (test.holds_iff (interpretation edges classFacts prepared) e.value).mp hholds⟩

private theorem atLeast_of_matchingValues {edges : List Edge} {classFacts : List ClassFact}
    {o : Ontology} {prepared : CompiledOntology o}
    {r : OrdinaryRole} {a : IRI} {t : DataRange} (test : DataRanges.Compiled t) {n : Nat}
    (h : n ≤ (matchingValues edges r a test.holds).length) :
    AtLeast n (fun y =>
      (interpretation edges classFacts prepared).dataProperties r.val
        ((interpretation edges classFacts prepared).individuals (.named a)) y ∧
      dataHolds (interpretation edges classFacts prepared) y t) := by
  let embed : Value → (interpretation edges classFacts prepared).Data :=
    (interpretation edges classFacts prepared).embedValue
  let vs := (matchingValues edges r a test.holds).take n
  refine ⟨vs.map embed, ?_, ?_, ?_⟩
  · rw [List.length_map, List.length_take, Nat.min_eq_left h]
  · exact nodup_map_injective Option.some.inj
      (List.Nodup.sublist (List.take_sublist n _) (dedup_nodup _))
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    exact matchingValues_sound test (List.mem_of_mem_take hv)

private theorem not_atLeast_of_matchingValues {edges : List Edge} {classFacts : List ClassFact}
    {o : Ontology} {prepared : CompiledOntology o}
    {r : OrdinaryRole} {a : IRI} {t : DataRange} (test : DataRanges.Compiled t) {n : Nat}
    (h : (matchingValues edges r a test.holds).length ≤ n) :
    ¬ AtLeast (n + 1) (fun y =>
      (interpretation edges classFacts prepared).dataProperties r.val
        ((interpretation edges classFacts prepared).individuals (.named a)) y ∧
      dataHolds (interpretation edges classFacts prepared) y t) := by
  let embed : Value → (interpretation edges classFacts prepared).Data :=
    (interpretation edges classFacts prepared).embedValue
  rintro ⟨xs, hlen, hnd, hp⟩
  have hsub : ∀ y ∈ xs, y ∈ (matchingValues edges r a test.holds).map embed := by
    intro y hy
    obtain ⟨hedge, hrange⟩ := hp y hy
    obtain ⟨(v : Value), rfl⟩ := embedded edges classFacts prepared r a y hedge
    refine List.mem_map.mpr ⟨v, ?_, rfl⟩
    apply mem_dedup.mpr
    refine List.mem_map.mpr ⟨⟨r.val, a, v⟩, ?_, rfl⟩
    apply List.mem_filter.mpr
    refine ⟨(ordinary_edge_iff edges classFacts prepared r a v).mp hedge, ?_⟩
    simp [(test.holds_iff (interpretation edges classFacts prepared) v).mpr hrange]
  have hle : xs.length ≤ ((matchingValues edges r a test.holds).map embed).length := by
    classical
    exact length_le_of_nodup_subset xs _ hnd hsub
  have hmap : ((matchingValues edges r a test.holds).map embed).length =
      (matchingValues edges r a test.holds).length := List.length_map ..
  omega

private def checkModelClause (edges : List Edge) (classFacts : List ClassFact) : Clause → Bool
  | .positive r a v => decide (⟨r.val,a,v⟩ ∈ edges)
  | .negative r a v => decide (⟨r.val,a,v⟩ ∉ edges)
  | .functional r => edges.all fun e => edges.all fun f =>
      decide (e.role = r.val → f.role = r.val → e.subject = f.subject → e.value = f.value)
  | .range r _ test _ _ => edges.all fun e =>
      e.role != r.val || test.holds e.value
  | .someRange r a _ solved => edges.any fun e =>
      e.role == r.val && e.subject == a && solved.compiled.holds e.value
  | .dataMin n r a _ solved => decide (n ≤ (matchingValues edges r a solved.compiled.holds).length)
  | .dataMax n r a _ test => decide ((matchingValues edges r a test.holds).length ≤ n)
  | .dataExact n r a _ solved => decide ((matchingValues edges r a solved.compiled.holds).length = n)
  | .classMember c a => decide (⟨c.val, a⟩ ∈ classFacts)
  | .subClassSomeIntInterval c r _ interval => classFacts.all fun f =>
      f.cls != c.val || edges.any fun e =>
        e.role == r.val && e.subject == f.subject && interval.compiled.holds e.value
  | .different inds => decide inds.Nodup
  | .hasKey c ds => classFacts.all fun f1 => classFacts.all fun f2 =>
      f1.cls != c.val || f2.cls != c.val || f1.subject == f2.subject ||
      !(ds.all fun r => edges.any fun e1 =>
        e1.role == r.val && e1.subject == f1.subject &&
        edges.any fun e2 => e2.role == r.val && e2.subject == f2.subject && e2.value == e1.value)
  | .datatypeDef _ _ => true

private theorem checkModelClause_sound {edges : List Edge} {classFacts : List ClassFact}
    {o : Ontology} {prepared : CompiledOntology o}
    {c : Clause} (hc_mem : c ∈ prepared.clauses)
    (hdef : ∀ d body, .datatypeDef d body ∈ prepared.clauses → prepared.defs.lookup d = some body)
    (h : checkModelClause edges classFacts c = true) :
    c.Holds (interpretation edges classFacts prepared) := by
  cases c with
  | positive r a v =>
    exact (ordinary_edge_iff edges classFacts prepared r a v).mpr (of_decide_eq_true h)
  | negative r a v =>
    exact fun hv => (of_decide_eq_true h) ((ordinary_edge_iff edges classFacts prepared r a v).mp hv)
  | functional r =>
    intro a v w hv hw
    have hall := List.all_eq_true.mp h _ ((ordinary_edge_iff edges classFacts prepared r a v).mp hv)
    have pair := of_decide_eq_true (List.all_eq_true.mp hall _
      ((ordinary_edge_iff edges classFacts prepared r a w).mp hw))
    exact pair rfl rfl rfl
  | range r t test _ _ =>
    intro a y hy
    obtain ⟨v, rfl⟩ := embedded edges classFacts prepared r a y hy
    have hall := List.all_eq_true.mp h _ ((ordinary_edge_iff edges classFacts prepared r a v).mp hy)
    exact (test.holds_iff (interpretation edges classFacts prepared) v).mp (by simpa using hall)
  | someRange r a t solved =>
    obtain ⟨e, he, hcond⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    rcases hcond with ⟨⟨hr, ha⟩, hholds⟩
    have hedge : (⟨r.val, a, e.value⟩ : Edge) ∈ edges := by
      rcases e with ⟨er, ea, ev⟩
      subst hr ha
      exact he
    exact ⟨(interpretation edges classFacts prepared).embedValue e.value,
      (ordinary_edge_iff edges classFacts prepared r a e.value).mpr hedge,
      (solved.compiled.holds_iff (interpretation edges classFacts prepared) e.value).mp hholds⟩
  | dataMin n r a t solved =>
    exact atLeast_of_matchingValues solved.compiled (of_decide_eq_true h)
  | dataMax n r a t test =>
    exact not_atLeast_of_matchingValues test (of_decide_eq_true h)
  | dataExact n r a t solved =>
    have heq : (matchingValues edges r a solved.compiled.holds).length = n := of_decide_eq_true h
    exact ⟨atLeast_of_matchingValues solved.compiled (Nat.le_of_eq heq.symm),
      not_atLeast_of_matchingValues solved.compiled (Nat.le_of_eq heq)⟩
  | classMember c a =>
    exact (ordinary_class_iff edges classFacts prepared c a).mpr (of_decide_eq_true h)
  | subClassSomeIntInterval c r t interval =>
    intro a ha
    have hmem : (⟨c.val, a⟩ : ClassFact) ∈ classFacts :=
      (ordinary_class_iff edges classFacts prepared c a).mp ha
    have hall := List.all_eq_true.mp h ⟨c.val, a⟩ hmem
    simp only [bne_self_eq_false, Bool.false_or] at hall
    obtain ⟨e, he, hcond⟩ := List.any_eq_true.mp hall
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    rcases hcond with ⟨⟨hr, ha'⟩, hholds⟩
    have ha'' : e.subject = a := beq_iff_eq.mp ha'
    have hedge : (⟨r.val, a, e.value⟩ : Edge) ∈ edges := by
      rcases e with ⟨er, ea, ev⟩
      subst hr ha''
      exact he
    exact ⟨(interpretation edges classFacts prepared).embedValue e.value,
      (ordinary_edge_iff edges classFacts prepared r a e.value).mpr hedge,
      (interval.compiled.holds_iff (interpretation edges classFacts prepared) e.value).mp hholds⟩
  | different inds =>
    exact (of_decide_eq_true h : inds.Nodup)
  | hasKey c ds =>
    intro (x : IRI) (y : IRI) hx hy _ _ hds
    have hfx : (⟨c.val, x⟩ : ClassFact) ∈ classFacts :=
      (ordinary_class_iff edges classFacts prepared c x).mp hx
    have hfy : (⟨c.val, y⟩ : ClassFact) ∈ classFacts :=
      (ordinary_class_iff edges classFacts prepared c y).mp hy
    have hstep := List.all_eq_true.mp (List.all_eq_true.mp h ⟨c.val, x⟩ hfx) ⟨c.val, y⟩ hfy
    simp only [bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hstep
    rcases hstep with hxy | hnotall
    · exact hxy
    · exfalso
      have hall : (ds.all fun r => edges.any fun e1 =>
          e1.role == r.val && e1.subject == x &&
          edges.any fun e2 => e2.role == r.val && e2.subject == y && e2.value == e1.value) = true := by
        apply List.all_eq_true.mpr
        intro r hr
        obtain ⟨z, hzx, hzy⟩ := hds r hr
        obtain ⟨(v : Value), rfl⟩ := embedded edges classFacts prepared r x z hzx
        have he1 : (⟨r.val, x, v⟩ : Edge) ∈ edges :=
          (ordinary_edge_iff edges classFacts prepared r x v).mp hzx
        have he2 : (⟨r.val, y, v⟩ : Edge) ∈ edges :=
          (ordinary_edge_iff edges classFacts prepared r y v).mp hzy
        apply List.any_eq_true.mpr
        refine ⟨⟨r.val, x, v⟩, he1, ?_⟩
        simp only [beq_self_eq_true, Bool.true_and]
        apply List.any_eq_true.mpr
        exact ⟨⟨r.val, y, v⟩, he2, by simp⟩
      rw [hall] at hnotall
      cases hnotall
  | datatypeDef d body =>
    exact defsHold_interpretation edges classFacts prepared d body (hdef d body hc_mem)

private def negativeCoversInt (cs : List Clause) (r : OrdinaryRole) (a : IRI)
    (negs : List Nat) (z : Int) : Bool :=
  negs.any fun m =>
    match cs[m]? with
    | some (.negative s b v) => decide (s = r ∧ b = a ∧ v = .integer z)
    | _ => false

private def extractDistinctValues (cs : List Clause) (r : OrdinaryRole) (a : IRI)
    (test : Value → Bool) : List Nat → Option (List Value)
  | [] => some []
  | m :: ms => do
    match cs[m]? with
    | some (.positive s b v) =>
      if s = r && b = a && test v then
        let rest ← extractDistinctValues cs r a test ms
        if v ∉ rest then some (v :: rest) else none
      else none
    | _ => none

private theorem extractDistinctValues_sound {cs : List Clause} {r : OrdinaryRole} {a : IRI}
    {t : DataRange} {test : DataRanges.Compiled t} {ms : List Nat} {vs : List Value}
    (h : extractDistinctValues cs r a test.holds ms = some vs)
    {j : Interpretation datatypeMap} (holds : ∀ c ∈ cs, c.Holds j) :
    vs.length = ms.length ∧ vs.Nodup ∧
      ∀ v ∈ vs, j.dataProperties r.val (j.individuals (.named a)) (j.embedValue v) ∧
        dataHolds j (j.embedValue v) t := by
  induction ms generalizing vs with
  | nil =>
    cases h
    exact ⟨rfl, List.nodup_nil, by simp⟩
  | cons m tail ih =>
    simp only [extractDistinctValues] at h
    split at h
    next s b v hm =>
      split at h
      · rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        rcases hcond with ⟨⟨rfl, rfl⟩, htest⟩
        obtain ⟨rest, hrest, hres⟩ := Option.bind_eq_some_iff.mp h
        split at hres
        · rename_i hnotmem
          cases hres
          obtain ⟨hlen, hnd, hall⟩ := ih hrest
          refine ⟨by simp [hlen], List.nodup_cons.mpr ⟨hnotmem, hnd⟩, ?_⟩
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact ⟨holds _ (List.mem_of_getElem? hm), (test.holds_iff j w).mp htest⟩
          · exact hall w hw'
        · cases hres
      · cases h
    next => cases h

private def keyPairMatches (cs : List Clause) (a b : IRI) (r : OrdinaryRole)
    (pairs : List (Nat × Nat)) : Bool :=
  pairs.any fun (pa, pb) =>
    match cs[pa]?, cs[pb]? with
    | some (.positive ra xa va), some (.positive rb xb vb) =>
      decide (ra = r ∧ rb = r ∧ xa = a ∧ xb = b ∧ va = vb)
    | _, _ => false

private theorem pairwise_ne_of_mem {α : Type} {p : α → α → Prop} {xs : List α}
    (hp : xs.Pairwise p) {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) :
    p a b ∨ p b a := by
  induction xs with
  | nil => cases ha
  | cons x tail ih =>
    have hcons := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact False.elim (hne rfl)
    · exact Or.inl (hcons.1 b hb')
    · exact Or.inr (hcons.1 a ha')
    · exact ih hcons.2 ha' hb'

private def checkPrepared (cs : List Clause) : Certificate → Bool
  | .model edges classFacts =>
    edges.all (fun e => decide (IsOrdinaryRole e.role)) &&
    classFacts.all (fun f => decide (IsOrdinaryClass f.cls)) &&
    cs.all (checkModelClause edges classFacts)
  | .functionalClash k n m =>
    match cs[k]?, cs[n]?, cs[m]? with
    | some (.functional r), some (.positive s a v), some (.positive t b w) =>
      decide (r = s ∧ r = t ∧ a = b ∧ v ≠ w)
    | _, _, _ => false
  | .rangeClash k n =>
    match cs[k]?, cs[n]? with
    | some (.range r _ test _ _), some (.positive s _ v) => decide (r = s) && !test.holds v
    | _, _ => false
  | .assertionClash n m =>
    match cs[n]?, cs[m]? with
    | some (.positive r a v), some (.negative s b w) => decide (r = s ∧ a = b ∧ v = w)
    | _, _ => false
  | .emptyRangeClash n lo hi =>
    match cs[n]? with
    | some (.someRange _ _ _ (.intInterval interval)) =>
      decide (interval.bounds.lower = some lo ∧ interval.bounds.upper = some hi ∧ hi < lo)
    | _ => false
  | .existentialRangeClash n k lo hi =>
    match cs[n]?, cs[k]? with
    | some (.someRange r _ _ (.intInterval i1)), some (.range s _ _ (some i2) _) =>
      let inter := i1.bounds.intersect i2.bounds
      decide (r = s ∧ inter.lower = some lo ∧ inter.upper = some hi ∧ hi < lo)
    | _, _ => false
  | .functionalExistentialClash k n m =>
    match cs[k]?, cs[n]?, cs[m]? with
    | some (.functional r), some (.someRange s a _ (.intInterval interval)), some (.positive t b v) =>
      decide (r = s ∧ r = t ∧ a = b) && !interval.compiled.holds v
    | _, _, _ => false
  | .negativeExistentialClash n negs lo hi =>
    match cs[n]? with
    | some (.someRange r a _ (.intInterval interval)) =>
      decide (interval.bounds.lower = some lo ∧ interval.bounds.upper = some hi ∧ lo ≤ hi) &&
      (List.range ((hi - lo).toNat + 1)).all fun offset =>
        negativeCoversInt cs r a negs (lo + offset)
    | _ => false
  | .subclassEmptyRangeClash k n lo hi =>
    match cs[k]?, cs[n]? with
    | some (.subClassSomeIntInterval c _ _ interval), some (.classMember d _) =>
      decide (c = d ∧ interval.bounds.lower = some lo ∧ interval.bounds.upper = some hi ∧ hi < lo)
    | _, _ => false
  | .emptySolvedRangeClash n =>
    match cs[n]? with
    | some (.someRange _ _ _ solved) => solved.isEmpty
    | _ => false
  | .existentialSolvedRangeClash n k =>
    match cs[n]?, cs[k]? with
    | some (.someRange r _ _ s1), some (.range s _ _ _ (some s2)) =>
      decide (r = s) && s1.disjoint s2
    | _, _ => false
  | .dataMaxClash k assertions =>
    match cs[k]? with
    | some (.dataMax n r a _ test) =>
      match extractDistinctValues cs r a test.holds assertions with
      | some vs => decide (vs.length = n + 1)
      | none => false
    | some (.dataExact n r a _ solved) =>
      match extractDistinctValues cs r a solved.compiled.holds assertions with
      | some vs => decide (vs.length = n + 1)
      | none => false
    | _ => false
  | .dataMinFiniteClash k =>
    match cs[k]? with
    | some (.dataMin n _ _ _ solved) | some (.dataExact n _ _ _ solved) =>
      match solved.finiteValues? with
      | some vs => decide (vs.length < n)
      | none => false
    | _ => false
  | .keyClash k d ma mb pairs =>
    match cs[k]?, cs[d]?, cs[ma]?, cs[mb]? with
    | some (.hasKey c ds), some (.different inds), some (.classMember ca a), some (.classMember cb b) =>
      decide (c = ca ∧ c = cb ∧ a ≠ b ∧ a ∈ inds ∧ b ∈ inds) &&
      ds.all (keyPairMatches cs a b · pairs)
    | _, _, _, _ => false

def check (o : Ontology) (cert : Certificate) : Bool :=
  match compile o with
  | some prepared => checkPrepared prepared.clauses cert
  | none => false

private theorem atLeast_contradicts_finite {j : Interpretation datatypeMap} {r : OrdinaryRole}
    {a : IRI} {t : DataRange} {solved : DataRanges.SolvedRange t} {n : Nat} {vs : List Value}
    (hvs : solved.finiteValues? = some vs) (hlt : vs.length < n)
    (hat : AtLeast n (fun y => j.dataProperties r.val (j.individuals (.named a)) y ∧ dataHolds j y t)) :
    False := by
  let embed : Value → j.Data := j.embedValue
  obtain ⟨xs, hlen, hnd, hp⟩ := hat
  have hsub : ∀ y ∈ xs, y ∈ vs.map embed := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := solved.finiteValues?_sound hvs j y (hp y hy).2
    exact List.mem_map_of_mem hv
  have hle : xs.length ≤ (vs.map embed).length := by
    classical
    exact length_le_of_nodup_subset xs (vs.map embed) hnd hsub
  rw [List.length_map] at hle
  omega

private theorem checkPrepared_sound {o : Ontology} (prepared : CompiledOntology o)
    {cert : Certificate} (h : checkPrepared prepared.clauses cert = true) : Claim o cert := by
  cases cert with
  | model edges classFacts =>
    simp only [checkPrepared, Bool.and_eq_true] at h
    exact ⟨interpretation edges classFacts prepared, satisfies_models (prepared.backward _
      (embedded edges classFacts prepared) (defsHold_interpretation edges classFacts prepared)
      (fun _ hc => checkModelClause_sound hc prepared.defs_clauses (List.all_eq_true.mp h.2 _ hc)))⟩
  | functionalClash k n m =>
    rintro ⟨i,assign,hs⟩
    let j := i.withAnonymous assign
    have holds := prepared.forward j hs
    simp only [checkPrepared] at h
    split at h
    next r s a v t b w hk hn hm =>
      obtain ⟨rfl,rfl,rfl,hne⟩ := of_decide_eq_true h
      exact hne (holds _ (List.mem_of_getElem? hk) (j.individuals (.named a)) v w
        (holds _ (List.mem_of_getElem? hn)) (holds _ (List.mem_of_getElem? hm)))
    next => contradiction
  | rangeClash k n =>
    rintro ⟨i,assign,hs⟩
    let j := i.withAnonymous assign
    have holds := prepared.forward j hs
    simp only [checkPrepared] at h
    split at h
    next r t test _ _ s a v hk hn =>
      rw [Bool.and_eq_true] at h
      obtain ⟨hr,hv⟩ := h
      have he : r = s := of_decide_eq_true hr
      subst s
      have hin := holds _ (List.mem_of_getElem? hk) (j.individuals (.named a)) (j.embedValue v)
        (holds _ (List.mem_of_getElem? hn))
      rw [(test.holds_iff j v).mpr hin] at hv
      contradiction
    next => contradiction
  | assertionClash n m =>
    rintro ⟨i,assign,hs⟩
    let j := i.withAnonymous assign
    have holds := prepared.forward j hs
    simp only [checkPrepared] at h
    split at h
    next r a v s b w hn hm =>
      obtain ⟨rfl,rfl,rfl⟩ := of_decide_eq_true h
      exact holds _ (List.mem_of_getElem? hm) (holds _ (List.mem_of_getElem? hn))
    next => contradiction
  | emptyRangeClash n lo hi =>
    rintro ⟨i,assign,hs⟩
    let j := i.withAnonymous assign
    have holds := prepared.forward j hs
    simp only [checkPrepared] at h
    split at h
    next r a t interval hn =>
      obtain ⟨hlo, hhi, hlt⟩ := of_decide_eq_true h
      obtain ⟨y, _, hy⟩ := holds _ (List.mem_of_getElem? hn)
      exact interval.empty_sound hlo hhi hlt j y hy
    next => contradiction
  | existentialRangeClash n k lo hi =>
    rintro ⟨i,assign,hs⟩
    let j := i.withAnonymous assign
    have holds := prepared.forward j hs
    simp only [checkPrepared] at h
    split at h
    next r a t1 i1 s t2 _ i2 _ hn hk =>
      obtain ⟨rfl, hlo, hhi, hlt⟩ := of_decide_eq_true h
      obtain ⟨y, hedge, hy1⟩ := holds _ (List.mem_of_getElem? hn)
      have hy2 := holds _ (List.mem_of_getElem? hk) (j.individuals (.named a)) y hedge
      exact i1.disjoint_sound i2 hlo hhi hlt j y ⟨hy1, hy2⟩
    next => contradiction
  | functionalExistentialClash k n m =>
    rintro ⟨i,assign,hs⟩
    let j := i.withAnonymous assign
    have holds := prepared.forward j hs
    simp only [checkPrepared] at h
    split at h
    next r s a t interval t' b v hk hn hm =>
      rw [Bool.and_eq_true] at h
      obtain ⟨heqs, hnot⟩ := h
      obtain ⟨rfl, rfl, rfl⟩ := of_decide_eq_true heqs
      obtain ⟨y, hedge, hy⟩ := holds _ (List.mem_of_getElem? hn)
      obtain ⟨z, _, rfl⟩ := interval.member_bounds j y hy
      have hpos := holds _ (List.mem_of_getElem? hm)
      have hveq : Value.integer z = v :=
        holds _ (List.mem_of_getElem? hk) (j.individuals (.named a)) (.integer z) v hedge hpos
      rw [hveq] at hy
      rw [(interval.compiled.holds_iff j v).mpr hy] at hnot
      contradiction
    next => contradiction
  | negativeExistentialClash n negs lo hi =>
    rintro ⟨i,assign,hs⟩
    let j := i.withAnonymous assign
    have holds := prepared.forward j hs
    simp only [checkPrepared] at h
    split at h
    next r a t interval hn =>
      rw [Bool.and_eq_true] at h
      obtain ⟨hbounds, hcov⟩ := h
      obtain ⟨hlo, hhi, hle⟩ := of_decide_eq_true hbounds
      obtain ⟨y, hedge, hy⟩ := holds _ (List.mem_of_getElem? hn)
      obtain ⟨z, hz, rfl⟩ := interval.member_bounds j y hy
      simp only [IntegerBounds.contains, hlo, hhi, Option.elim] at hz
      have hmem : (z - lo).toNat ∈ List.range ((hi - lo).toNat + 1) := by
        rw [List.mem_range]
        omega
      have hstep := List.all_eq_true.mp hcov _ hmem
      have hsum : lo + ((z - lo).toNat : Int) = z := by omega
      rw [hsum] at hstep
      obtain ⟨m, _, hm⟩ := List.any_eq_true.mp hstep
      split at hm
      next s b v hget =>
        obtain ⟨rfl, rfl, rfl⟩ := of_decide_eq_true hm
        exact holds _ (List.mem_of_getElem? hget) hedge
      next => contradiction
    next => contradiction
  | subclassEmptyRangeClash k n lo hi =>
    rintro ⟨i,assign,hs⟩
    let j := i.withAnonymous assign
    have holds := prepared.forward j hs
    simp only [checkPrepared] at h
    split at h
    next c r t interval d a hk hn =>
      obtain ⟨rfl, hlo, hhi, hlt⟩ := of_decide_eq_true h
      have hmem := holds _ (List.mem_of_getElem? hn)
      obtain ⟨y, _, hy⟩ := holds _ (List.mem_of_getElem? hk) (j.individuals (.named a)) hmem
      exact interval.empty_sound hlo hhi hlt j y hy
    next => contradiction
  | emptySolvedRangeClash n =>
    rintro ⟨i,assign,hs⟩
    let j := i.withAnonymous assign
    have holds := prepared.forward j hs
    simp only [checkPrepared] at h
    split at h
    next r a t solved hn =>
      obtain ⟨y, _, hy⟩ := holds _ (List.mem_of_getElem? hn)
      exact solved.isEmpty_sound h j y hy
    next => contradiction
  | existentialSolvedRangeClash n k =>
    rintro ⟨i,assign,hs⟩
    let j := i.withAnonymous assign
    have holds := prepared.forward j hs
    simp only [checkPrepared] at h
    split at h
    next r a t1 s1 s t2 _ _ s2 hn hk =>
      rw [Bool.and_eq_true] at h
      obtain ⟨hr, hdisj⟩ := h
      have heq : r = s := of_decide_eq_true hr
      subst s
      obtain ⟨y, hedge, hy1⟩ := holds _ (List.mem_of_getElem? hn)
      have hy2 := holds _ (List.mem_of_getElem? hk) (j.individuals (.named a)) y hedge
      exact s1.disjoint_sound s2 hdisj j y ⟨hy1, hy2⟩
    next => contradiction
  | dataMaxClash k assertions =>
    rintro ⟨i,assign,hs⟩
    let j := i.withAnonymous assign
    let embed : Value → j.Data := j.embedValue
    have holds := prepared.forward j hs
    simp only [checkPrepared] at h
    split at h
    next n r a t test hk =>
      split at h
      next vs hvs =>
        have hlen : vs.length = n + 1 := of_decide_eq_true h
        obtain ⟨_, hnd, hall⟩ := extractDistinctValues_sound hvs holds
        apply holds _ (List.mem_of_getElem? hk)
        refine ⟨vs.map embed, by rw [List.length_map, hlen],
          nodup_map_injective j.embedValue_injective hnd, ?_⟩
        intro y hy
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
        exact hall v hv
      next => contradiction
    next n r a t solved hk =>
      split at h
      next vs hvs =>
        have hlen : vs.length = n + 1 := of_decide_eq_true h
        obtain ⟨_, hnd, hall⟩ := extractDistinctValues_sound hvs holds
        apply (holds _ (List.mem_of_getElem? hk)).2
        refine ⟨vs.map embed, by rw [List.length_map, hlen],
          nodup_map_injective j.embedValue_injective hnd, ?_⟩
        intro y hy
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
        exact hall v hv
      next => contradiction
    next => contradiction
  | dataMinFiniteClash k =>
    rintro ⟨i,assign,hs⟩
    let j := i.withAnonymous assign
    have holds := prepared.forward j hs
    simp only [checkPrepared] at h
    split at h
    next n r a t solved hk =>
      split at h
      next vs hvs =>
        exact atLeast_contradicts_finite hvs (of_decide_eq_true h)
          (holds _ (List.mem_of_getElem? hk))
      next => contradiction
    next n r a t solved hk =>
      split at h
      next vs hvs =>
        exact atLeast_contradicts_finite hvs (of_decide_eq_true h)
          (holds _ (List.mem_of_getElem? hk)).1
      next => contradiction
    next => contradiction
  | keyClash k d ma mb pairs =>
    rintro ⟨i,assign,hs⟩
    let j := i.withAnonymous assign
    have holds := prepared.forward j hs
    simp only [checkPrepared] at h
    split at h
    next c ds inds ca a cb b hk hd hma hmb =>
      rw [Bool.and_eq_true] at h
      obtain ⟨hcond, hpairs⟩ := h
      obtain ⟨rfl, rfl, hne, ha, hb⟩ := of_decide_eq_true hcond
      have hkey := holds _ (List.mem_of_getElem? hk)
      have hdiff := holds _ (List.mem_of_getElem? hd)
      have hmA := holds _ (List.mem_of_getElem? hma)
      have hmB := holds _ (List.mem_of_getElem? hmb)
      have heq : j.individuals (.named a) = j.individuals (.named b) := by
        apply hkey _ _ hmA hmB (j.namedIndividual a) (j.namedIndividual b)
        intro r hr
        have hm := List.all_eq_true.mp hpairs r hr
        simp only [keyPairMatches] at hm
        obtain ⟨⟨pa, pb⟩, _, hmatch⟩ := List.any_eq_true.mp hm
        split at hmatch
        next ra xa va rb xb vb hpa hpb =>
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := of_decide_eq_true hmatch
          exact ⟨j.embedValue va, holds _ (List.mem_of_getElem? hpa), holds _ (List.mem_of_getElem? hpb)⟩
        next => contradiction
      rcases pairwise_ne_of_mem hdiff ha hb hne with h1 | h2
      · exact h1 heq
      · exact h2 heq.symm
    next => contradiction

theorem check_sound {o : Ontology} {cert : Certificate} (h : check o cert = true) :
    Claim o cert := by
  unfold check at h
  split at h
  next prepared _ => exact checkPrepared_sound prepared h
  next => contradiction

inductive Result where
  | checked (cert : Certificate)
  | unsupported
  | unknown
  deriving DecidableEq, Repr

private def Clause.edge? : Clause → Option Edge
  | .positive r a v => some ⟨r.val,a,v⟩
  | _ => none

private def Clause.classFact? : Clause → Option ClassFact
  | .classMember c a => some ⟨c.val, a⟩
  | _ => none

private def collectDistinctAssertionIndices (positives : List (Edge × Nat))
    (r : OrdinaryRole) (a : IRI) (test : Value → Bool) (target : Nat) : Option (List Nat) :=
  let rec loop : List (Edge × Nat) → List Value → List Nat → Option (List Nat)
    | [], _, acc => if acc.length == target then some acc.reverse else none
    | (e, idx) :: rest, seen, acc =>
      if acc.length == target then some acc.reverse
      else if e.role == r.val && e.subject == a && test e.value && !(seen.contains e.value) then
        loop rest (e.value :: seen) (idx :: acc)
      else loop rest seen acc
  loop positives [] []

/-- Look only at the premise shapes used by each clash constructor. -/
private def searchClash (cs : List Clause) : Option Certificate :=
  let positions := cs.zipIdx
  let positives := positions.filterMap fun (c, n) => c.edge?.map fun e => (e, n)
  let classMembers := positions.filterMap fun (c, n) => c.classFact?.map fun f => (f, n)
  positions.findSome? fun (c, k) =>
    match c with
    | .functional r =>
      let matching := positives.filter fun (e, _) => e.role == r.val
      (matching.findSome? fun (e, n) =>
        matching.findSome? fun (f, m) =>
          if n < m ∧ e.subject = f.subject ∧ e.value ≠ f.value then
            some (.functionalClash k n m)
          else none) <|>
      (positions.findSome? fun (c', n) =>
        match c' with
        | .someRange s a _ (.intInterval interval) =>
          if s = r then
            matching.findSome? fun (e, m) =>
              if e.subject = a && !interval.compiled.holds e.value then
                some (.functionalExistentialClash k n m)
              else none
          else none
        | _ => none)
    | .range r _ test _ _ =>
      positives.findSome? fun (e, n) =>
        if e.role == r.val && !test.holds e.value then some (.rangeClash k n) else none
    | .negative r a v =>
      positives.findSome? fun (e, n) =>
        if e.role = r.val ∧ e.subject = a ∧ e.value = v then some (.assertionClash n k) else none
    | .someRange r a _ solved =>
      let intClashes :=
        match solved with
        | .intInterval interval =>
          (match interval.bounds.lower, interval.bounds.upper with
           | some lo, some hi =>
             if hi < lo then some (.emptyRangeClash k lo hi) else none
           | _, _ => none) <|>
          (positions.findSome? fun (c', m) =>
            match c' with
            | .range s _ _ (some rangeInterval) _ =>
              if s = r then
                let inter := interval.bounds.intersect rangeInterval.bounds
                match inter.lower, inter.upper with
                | some lo, some hi =>
                  if hi < lo then some (.existentialRangeClash k m lo hi) else none
                | _, _ => none
              else none
            | _ => none) <|>
          (match interval.bounds.lower, interval.bounds.upper with
           | some lo, some hi =>
             if lo ≤ hi then
               let matchingNegs := positions.filterMap fun (c', m) =>
                 match c' with
                 | .negative s b _ => if s = r && b = a then some m else none
                 | _ => none
               if (hi - lo).toNat ≤ matchingNegs.length &&
                  (List.range ((hi - lo).toNat + 1)).all (fun offset =>
                    negativeCoversInt cs r a matchingNegs (lo + offset)) then
                 some (.negativeExistentialClash k matchingNegs lo hi)
               else none
             else none
           | _, _ => none)
        | _ =>
          if solved.isEmpty then some (.emptySolvedRangeClash k) else none
      intClashes <|>
      (positions.findSome? fun (c', m) =>
        match c' with
        | .range s _ _ _ (some rangeSolved) =>
          if s = r && solved.disjoint rangeSolved then
            some (.existentialSolvedRangeClash k m)
          else none
        | _ => none)
    | .dataMin n _ _ _ solved =>
      match solved.finiteValues? with
      | some vs => if vs.length < n then some (.dataMinFiniteClash k) else none
      | none => none
    | .dataMax n r a _ test =>
      (collectDistinctAssertionIndices positives r a test.holds (n + 1)).map (.dataMaxClash k)
    | .dataExact n r a _ solved =>
      (match solved.finiteValues? with
       | some vs => if vs.length < n then some (.dataMinFiniteClash k) else none
       | none => none) <|>
      (collectDistinctAssertionIndices positives r a solved.compiled.holds (n + 1)).map (.dataMaxClash k)
    | .subClassSomeIntInterval c _ _ interval =>
      match interval.bounds.lower, interval.bounds.upper with
      | some lo, some hi =>
        if hi < lo then
          classMembers.findSome? fun (f, m) =>
            if f.cls == c.val then some (.subclassEmptyRangeClash k m lo hi) else none
        else none
      | _, _ => none
    | .hasKey c ds =>
      positions.findSome? fun (c', d) =>
        match c' with
        | .different inds =>
          classMembers.findSome? fun (fa, ma) =>
            if fa.cls == c.val && inds.contains fa.subject then
              classMembers.findSome? fun (fb, mb) =>
                if fb.cls == c.val && fb.subject != fa.subject && inds.contains fb.subject then
                  let matchedPairs := ds.map fun r =>
                    positives.findSome? fun (ea, pa) =>
                      if ea.role == r.val && ea.subject == fa.subject then
                        positives.findSome? fun (eb, pb) =>
                          if eb.role == r.val && eb.subject == fb.subject && eb.value == ea.value then
                            some (pa, pb)
                          else none
                      else none
                  if matchedPairs.all Option.isSome then
                    some (.keyClash k d ma mb (matchedPairs.filterMap id))
                  else none
                else none
            else none
        | _ => none
    | .positive .. | .classMember .. | .different .. | .datatypeDef .. => none

private def ratFloor (q : Rat) : Int := Int.ediv q.num q.den

private def dyadicCandidates (lo hi : Rat) (count : Nat) : List Rat :=
  let diffNum : Int := hi.num * (lo.den : Int) - lo.num * (hi.den : Int)
  let diffDen : Int := (hi.den * lo.den : Nat)
  let rec findStep : Nat → Nat → Nat
    | 0, den => den
    | p + 1, den =>
      if ((count + 2 : Int) * diffDen) < diffNum * (den : Int) then den
      else findStep p (den * 2)
  let den := findStep 40 1
  let baseNum := Int.ediv (lo.num * (den : Int)) (lo.den : Int) + 1
  (List.range count).map fun (k : Nat) => mkRat (baseNum + (k : Int)) den

private def ratCandidates (bounds : DataRanges.RatBounds) (decimalOnly : Bool) (count : Nat) : List Value :=
  if bounds.isEmpty decimalOnly then []
  else
    let qs : List Rat :=
      match bounds.lower, bounds.upper with
      | some lb, some ub =>
        if lb.value == ub.value then [lb.value]
        else
          let interior := dyadicCandidates lb.value ub.value count
          (if lb.inclusive then [lb.value] else []) ++ interior ++ (if ub.inclusive then [ub.value] else [])
      | some lb, none =>
        let start := ratFloor lb.value + 1
        (if lb.inclusive then [lb.value] else []) ++
          (List.range count).map fun (k : Nat) => Rat.ofInt (start + (k : Int))
      | none, some ub =>
        let start := ratFloor ub.value - 1
        (if ub.inclusive then [ub.value] else []) ++
          (List.range count).map fun (k : Nat) => Rat.ofInt (start - (k : Int))
      | none, none =>
        (List.range count).map fun (k : Nat) => Rat.ofInt (k : Int)
    (qs.eraseDups).map Value.number

private def stringCandidates (bounds : DataRanges.StringLengthBounds) (count : Nat) : List Value :=
  if bounds.isEmpty then []
  else if bounds.minLen == 0 && bounds.maxLen == some 0 then [.string ""]
  else
    let len := if bounds.minLen == 0 then 1 else bounds.minLen
    let prefixChars := List.replicate (len - 1) 'a'
    (List.range count).map fun k =>
      let ch := Char.ofNat (97 + (k % 26))
      Value.string (String.ofList (prefixChars ++ [ch]))

private def pickSolvedWitnesses {t : DataRange} (cs : List Clause) (r : OrdinaryRole) (a : IRI)
    (solved : DataRanges.SolvedRange t) (existing : List Edge) (needed : Nat) : List Value :=
  let already := matchingValues existing r a solved.compiled.holds
  if needed ≤ already.length then []
  else
    let missing := needed - already.length
    let rangeTests : List (Value → Bool) := cs.filterMap fun
      | .range s _ test _ _ => if s = r then some test.holds else none
      | _ => none
    let negCount := (cs.filter fun
      | .negative s b _ => s = r && b = a
      | _ => false).length
    let isAllowed (v : Value) : Bool :=
      !(already.contains v) && solved.compiled.holds v &&
      rangeTests.all (fun f => f v) &&
      cs.all fun
        | .negative s b w => !(s = r && b = a && w = v)
        | _ => true
    let budget := missing + negCount + already.length + 2
    let candidates : List Value :=
      match solved with
      | .finite f => f.values.eraseDups
      | .intInterval iv =>
        let combined := cs.foldl (fun acc c =>
          match c with
          | .range s _ _ (some ri) _ => if s = r then acc.intersect ri.bounds else acc
          | _ => acc) iv.bounds
        let ints : List Int :=
          match combined.lower, combined.upper with
          | some lo, _ => (List.range budget).map fun (k : Nat) => lo + (k : Int)
          | none, some hi => (List.range budget).map fun (k : Nat) => hi - (k : Int)
          | none, none => (List.range budget).map fun (k : Nat) => (k : Int)
        ints.map Value.integer
      | .ratInterval rv => ratCandidates rv.bounds rv.decimalOnly budget
      | .stringInterval sv => stringCandidates sv.bounds budget
    (candidates.filter isAllowed).eraseDups.take missing

private def pickIntWitness (cs : List Clause) (r : OrdinaryRole) (a : IRI)
    (bounds : IntegerBounds) (test : Value → Bool) : Option Value :=
  let combined := cs.foldl (fun acc c =>
    match c with
    | .range s _ _ (some ri) _ => if s = r then acc.intersect ri.bounds else acc
    | _ => acc) bounds
  let rangeTests : List (Value → Bool) := cs.filterMap fun
    | .range s _ t _ _ => if s = r then some t.holds else none
    | _ => none
  let negCount := (cs.filter fun
    | .negative s b _ => s = r && b = a
    | _ => false).length
  let isAllowed (z : Int) : Bool :=
    let v := Value.integer z
    decide (combined.contains z) && test v &&
    rangeTests.all (fun f => f v) &&
    cs.all fun
      | .negative s b w => !(s = r && b = a && w = v)
      | _ => true
  let candidates : List Int :=
    match combined.lower, combined.upper with
    | some lo, _ => (List.range (negCount + 1)).map fun (k : Nat) => lo + (k : Int)
    | none, some hi => (List.range (negCount + 1)).map fun (k : Nat) => hi - (k : Int)
    | none, none => (List.range (negCount + 1)).map fun (k : Nat) => (k : Int)
  (candidates.find? isAllowed).map Value.integer

private def proposeModel (cs : List Clause) : Certificate :=
  let base := (cs.filterMap Clause.edge?).eraseDups
  let classFacts := (cs.filterMap Clause.classFact?).eraseDups
  let edgesAfterDirect := cs.foldl (fun acc c =>
    match c with
    | .someRange r a _ solved =>
      let ws := pickSolvedWitnesses cs r a solved acc 1
      (acc ++ ws.map fun v => Edge.mk r.val a v).eraseDups
    | .dataMin n r a _ solved | .dataExact n r a _ solved =>
      let ws := pickSolvedWitnesses cs r a solved acc n
      (acc ++ ws.map fun v => Edge.mk r.val a v).eraseDups
    | _ => acc) base
  let subWitnesses := cs.flatMap fun
    | .subClassSomeIntInterval c r _ interval =>
      classFacts.filterMap fun f =>
        if f.cls == c.val then
          if edgesAfterDirect.any (fun e => e.role == r.val && e.subject == f.subject && interval.compiled.holds e.value) then
            none
          else (pickIntWitness cs r f.subject interval.bounds interval.compiled.holds).map fun v =>
            ⟨r.val, f.subject, v⟩
        else none
    | _ => []
  .model (edgesAfterDirect ++ subWitnesses).eraseDups classFacts

private def solvePrepared (cs : List Clause) : Result :=
  let model := proposeModel cs
  if checkPrepared cs model then .checked model
  else match searchClash cs with
    | some cert => if checkPrepared cs cert then .checked cert else .unknown
    | none => .unknown

def solve (o : Ontology) : Result :=
  match compile o with
  | some prepared => solvePrepared prepared.clauses
  | none => .unsupported

theorem solve_checked {o : Ontology} {cert : Certificate} (h : solve o = .checked cert) :
    check o cert = true := by
  unfold solve at h
  split at h
  next prepared hp =>
    simp only [solvePrepared] at h
    simp only [check, hp]
    split at h
    next hc => cases h; exact hc
    next =>
      split at h
      next =>
        split at h
        next hc => cases h; exact hc
        next => contradiction
      next => contradiction
  next => contradiction

theorem solve_sound {o : Ontology} {cert : Certificate} (h : solve o = .checked cert) :
    Claim o cert :=
  check_sound (solve_checked h)

end Sabrina.OWL2.DataCertificates
