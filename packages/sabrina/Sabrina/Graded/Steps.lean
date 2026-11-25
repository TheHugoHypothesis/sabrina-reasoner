import Sabrina.Graded.Branch

namespace Sabrina.Graded

open ALC RoleChains

/-- A transition computes its successors and carries a proof that a model of
    the current branch realizes at least one successor. The proof is erased
    during execution. An empty successor list is therefore a certified clash. -/
structure Transition (p : Problem) (s : Branch) where
  branches : List Branch
  preserves : s.Sat p → ∃ t ∈ branches, t.Sat p

private def deterministic {p : Problem} {s : Branch} (t : Branch)
    (h : s.Sat p → t.Sat p) : Transition p s :=
  ⟨[t],fun hs => ⟨t,List.mem_singleton.mpr rfl,h hs⟩⟩

private def close {p : Problem} {s : Branch} (h : ¬ s.Sat p) : Transition p s :=
  ⟨[],fun hs => (h hs).elim⟩

private def add {p : Problem} {s : Branch} (x : Nat) (c : Concept)
    (h : ∀ (i : Interpretation) (nom : String → i.Domain) (env : Nat → i.Domain),
      Graded.models i nom p.tbox → s.Realizes i nom env → Graded.holds i nom (env x) c) :
    Transition p s :=
  deterministic (s.add x c) fun ⟨i,nom,hr,hc,hrc,ht,env,hs⟩ =>
    ⟨i,nom,hr,hc,hrc,ht,env,Branch.add_realizes hs (h i nom env ht hs)⟩

private def select {p : Problem} {s : Branch} (x : Nat) (a b : Concept)
    (h : ∀ (i : Interpretation) (nom : String → i.Domain) (env : Nat → i.Domain),
      Graded.models i nom p.tbox → s.Realizes i nom env →
        Graded.holds i nom (env x) a ∨ Graded.holds i nom (env x) b) : Transition p s :=
  ⟨[s.add x a,s.add x b],fun ⟨i,nom,hr,hc,hrc,ht,env,hs⟩ => by
    rcases h i nom env ht hs with ha | hb
    · exact ⟨s.add x a,by simp,i,nom,hr,hc,hrc,ht,env,Branch.add_realizes hs ha⟩
    · exact ⟨s.add x b,by simp,i,nom,hr,hc,hrc,ht,env,Branch.add_realizes hs hb⟩⟩

private def addEdge {p : Problem} {s : Branch} (r : OrientedRole) (x y : Nat)
    (h : ∀ (i : Interpretation) (nom : String → i.Domain) (env : Nat → i.Domain),
      modelsRoles i p.rules → modelsChains i p.chains → modelsRoleChars i p.chars →
      s.Realizes i nom env → holdsRole i r (env x) (env y)) : Transition p s :=
  deterministic (s.addOriented r x y) fun ⟨i,nom,hr,hc,hrc,ht,env,hs⟩ =>
    ⟨i,nom,hr,hc,hrc,ht,env,Branch.addOriented_realizes hs (h i nom env hr hc hrc hs)⟩

private def inequalityClash (p : Problem) (s : Branch) : Option (Transition p s) :=
  s.unequal.attach.findSome? fun ⟨⟨x,y⟩,h⟩ =>
    if he : x = y then some (close fun ⟨_,_,_,_,_,_,env,hs⟩ => hs.2.2.1 x y h (congrArg env he))
    else none

private def labelClash (p : Problem) (s : Branch) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨⟨x,c⟩,h⟩ =>
    if hc : c = .bottom then
      some (close fun ⟨i,nom,_,_,_,_,env,hs⟩ => by
        have he := hs.1 x c h
        rw [hc] at he
        exact he)
    else if hd : s.known x c.dual then
      some (close fun ⟨i,nom,_,_,_,_,env,hs⟩ =>
        (holds_dual i nom (env x) c).mp (Branch.known_sound hs hd) (hs.1 x c h))
    else none

private def nominalMerge (p : Problem) (s : Branch) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨⟨x,c⟩,h⟩ =>
    match c with
    | .nom a true =>
      s.noms.attach.findSome? fun ⟨⟨b,y⟩,hn⟩ =>
        if hab : a = b then
          if hxy : x ≠ y then
            let keep := min x y
            let drop := max x y
            some (deterministic (s.merge keep drop) fun ⟨i,nom,hr,hc,hrc,ht,env,hs⟩ => by
              have hx : env x = nom a := hs.1 x (.nom a true) h
              have hy : env y = nom a := hab ▸ hs.2.2.2 b y hn
              have heq : env keep = env drop := by
                by_cases hle : x ≤ y
                · simp only [keep, drop, Nat.min_eq_left hle, Nat.max_eq_right hle]
                  exact hx.trans hy.symm
                · have hlt : y ≤ x := Nat.le_of_not_le hle
                  simp only [keep, drop, Nat.min_eq_right hlt, Nat.max_eq_left hlt]
                  exact hy.trans hx.symm
              exact ⟨i,nom,hr,hc,hrc,ht,env,Branch.merge_realizes hs heq⟩)
          else none
        else none
    | .nom a false =>
      s.noms.attach.findSome? fun ⟨⟨b,y⟩,hn⟩ =>
        if hab : a = b then
          if hxy : x = y then
            some (close fun ⟨i,nom,_,_,_,_,env,hs⟩ => by
              have hx : env x ≠ nom a := hs.1 x (.nom a false) h
              have hy : env x = nom a := hxy ▸ hab ▸ hs.2.2.2 b y hn
              exact hx hy)
          else none
        else none
    | _ => none

private def selfSteps (p : Problem) (s : Branch) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨⟨x,c⟩,h⟩ =>
    match c with
    | .self r true =>
      if s.edge (r,false) x x then none
      else some (addEdge (r,false) x x fun _ _ _ _ _ _ hs => hs.1 x (.self r true) h)
    | .self r false =>
      if he : s.edge (r,false) x x then
        some (close fun ⟨_,_,_,_,_,_,_,hs⟩ => hs.1 x (.self r false) h (Branch.edge_sound hs he))
      else none
    | _ => none

private def roleCharSteps (p : Problem) (s : Branch) (nodes : List Nat) : Option (Transition p s) :=
  (p.chars.irreflexive.attach.findSome? fun ⟨r, hr⟩ =>
    nodes.findSome? fun x =>
      if he : s.edge (r,false) x x then
        some (close fun ⟨_,_,_,_,hrc,_,_,hs⟩ => hrc.2.1 r hr _ (Branch.edge_sound hs he))
      else none) <|>
  (p.chars.asymmetric.attach.findSome? fun ⟨r, hr⟩ =>
    nodes.findSome? fun x => nodes.findSome? fun y =>
      if hxy : s.edge (r,false) x y then
        if hyx : s.edge (r,false) y x then
          some (close fun ⟨_,_,_,_,hrc,_,_,hs⟩ =>
            hrc.2.2.1 r hr _ _ (Branch.edge_sound hs hxy) (Branch.edge_sound hs hyx))
        else none
      else none) <|>
  (p.chars.disjoint.attach.findSome? fun ⟨(r,t), hd⟩ =>
    nodes.findSome? fun x => nodes.findSome? fun y =>
      if hr : s.edge r x y then
        if ht : s.edge t x y then
          some (close fun ⟨_,_,_,_,hrc,_,_,hs⟩ =>
            hrc.2.2.2 (r,t) hd _ _ ⟨Branch.edge_sound hs hr, Branch.edge_sound hs ht⟩)
        else none
      else none) <|>
  (p.chars.reflexive.attach.findSome? fun ⟨r, hr⟩ =>
    nodes.findSome? fun x =>
      if s.edge (r,false) x x then none
      else some (addEdge (r,false) x x fun _ _ _ _ _ hrc _ => hrc.1 r hr _))

private def hierarchy (p : Problem) (s : Branch) (nodes : List Nat) : Option (Transition p s) :=
  p.rules.attach.findSome? fun ⟨(r,t),h⟩ =>
    nodes.findSome? fun x => nodes.findSome? fun y =>
      if hs : s.edge r x y then
        if s.edge t x y then none
        else some (addEdge t x y fun _ _ env hr _ _ he => hr r t h (env x) (env y) (Branch.edge_sound he hs))
      else none

private def chains (p : Problem) (s : Branch) (nodes : List Nat) : Option (Transition p s) :=
  p.chains.attach.findSome? fun ⟨c,hc⟩ =>
    nodes.findSome? fun x =>
      (s.targets x c.body).attach.findSome? fun ⟨y,hy⟩ =>
        if s.edge (c.head,false) x y then none
        else some (addEdge (c.head,false) x y fun _ _ env _ hc' _ hs =>
          hc' c hc (env x) (env y) (Branch.targets_sound hs hy))

private def localLabels (p : Problem) (s : Branch) (nodes : List Nat) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨(x,c),h⟩ =>
    match c with
    | .conj a b =>
      if !s.known x a then some (add x a fun _ _ _ _ hs => (hs.1 x (.conj a b) h).1)
      else if !s.known x b then some (add x b fun _ _ _ _ hs => (hs.1 x (.conj a b) h).2)
      else none
    | .all r c =>
      nodes.findSome? fun y =>
        if he : s.edge (r,false) x y then
          if s.known y c then none
          else some (add y c fun _ _ env _ hs => hs.1 x (.all r c) h (env y) (Branch.edge_sound hs he))
        else none
    | _ => none

private def deterministicGCI (p : Problem) (s : Branch) (nodes : List Nat) :
    Option (Transition p s) :=
  nodes.findSome? fun x => p.tbox.attach.findSome? fun ⟨q,hq⟩ =>
    if s.known x q.sup then none
    else if hh : s.known x q.sub then
      some (add x q.sup fun _ _ env ht hs => ht q hq (env x) (Branch.known_sound hs hh))
    else none

private def disjunctions (p : Problem) (s : Branch) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨(x,c),h⟩ =>
    match c with
    | .disj a b =>
      if s.known x a || s.known x b then none
      else if ha : s.known x a.dual then
        some (add x b fun i nom env _ hs =>
          (hs.1 x (.disj a b) h).resolve_left ((holds_dual i nom (env x) a).mp (Branch.known_sound hs ha)))
      else if hb : s.known x b.dual then
        some (add x a fun i nom env _ hs =>
          (hs.1 x (.disj a b) h).resolve_right ((holds_dual i nom (env x) b).mp (Branch.known_sound hs hb)))
      else some (select x a b fun _ _ _ _ hs => hs.1 x (.disj a b) h)
    | _ => none

private def splitClass {p : Problem} {s : Branch} (x : Nat) (a : Concept) : Transition p s :=
  select x a a.dual fun i nom env _ _ => by
    classical
    rcases Classical.em (Graded.holds i nom (env x) a) with h | h
    · exact Or.inl h
    · exact Or.inr ((holds_dual i nom (env x) a).mpr h)

private def undecidedGCI (p : Problem) (s : Branch) (nodes : List Nat) :
    Option (Transition p s) :=
  nodes.findSome? fun x => p.tbox.attach.findSome? fun ⟨q,hq⟩ =>
    if s.known x q.sup || s.known x q.sub.dual then none
    else some (select x q.sub.dual q.sup fun i nom env ht _ => by
      classical
      rcases Classical.em (Graded.holds i nom (env x) q.sub) with ha | ha
      · exact Or.inr (ht q hq (env x) ha)
      · exact Or.inl ((holds_dual i nom (env x) q.sub).mpr ha))

private def qualifiers (p : Problem) (s : Branch) (nodes : List Nat) : Option (Transition p s) :=
  s.labels.findSome? fun (x,c) =>
    match c with
    | .max _ r body =>
      nodes.findSome? fun y =>
        if s.edge (r,false) x y && !(s.known y body || s.known y body.dual) then
          some (splitClass y body)
        else none
    | _ => none

private def mergeChoices {p : Problem} {s : Branch} {x n : Nat} {r : String} {c : Concept}
    (label : (x,.max n r c) ∈ s.labels) (nodes : List Nat)
    (hlen : nodes.length = n + 1) (hn : nodes.Nodup)
    (qualified : ∀ y ∈ nodes, s.edge (r,false) x y = true ∧ s.known y c = true) :
    Transition p s :=
  let pairs := (distinctPairs nodes).filter fun (a,b) => decide (a < b)
  ⟨pairs.map (fun (a,b) => s.merge a b),fun hs => by
    obtain ⟨i,nom,hr,hc,hrc,ht,env,h⟩ := hs
    have he (y : Nat) (hy : y ∈ nodes) : i.role r (env x) (env y) ∧ Graded.holds i nom (env y) c :=
      ⟨Branch.edge_sound h (qualified y hy).1,Branch.known_sound h (qualified y hy).2⟩
    obtain ⟨a,ha,b,hb,hab,heq⟩ :=
      exists_equal_witnesses hlen hn he (h.1 x (.max n r c) label)
    have takePair (a b : Nat) (ha : a ∈ nodes) (hb : b ∈ nodes) (hlt : a < b)
        (he : env a = env b) : ∃ t ∈ pairs.map (fun (a,b) => s.merge a b), t.Sat p := by
      have hp : (a,b) ∈ pairs := List.mem_filter.mpr
        ⟨mem_distinctPairs.mpr ⟨ha,hb,Nat.ne_of_lt hlt⟩,decide_eq_true hlt⟩
      exact ⟨s.merge a b,List.mem_map.mpr ⟨(a,b),hp,rfl⟩,i,nom,hr,hc,hrc,ht,env,
        Branch.merge_realizes h he⟩
    exact (Nat.lt_or_gt_of_ne hab).elim (fun hlt => takePair a b ha hb hlt heq)
      (fun hlt => takePair b a hb ha hlt heq.symm)⟩

private def upperBounds (p : Problem) (s : Branch) : Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨(x,c),h⟩ =>
    match c with
    | .max n r body =>
      let qualified := s.nodes.filter fun y => s.edge (r,false) x y && s.known y body
      if hn : n + 1 ≤ qualified.length then
        let ys := qualified.take (n + 1)
        some (mergeChoices h ys (List.length_take_of_le hn)
          ((List.take_sublist ..).nodup (List.filter_sublist.nodup s.nodes_nodup))
          (fun _ hy => Bool.and_eq_true_iff.mp ((List.mem_filter.mp (List.mem_of_mem_take hy)).2)))
      else none
    | _ => none

private def witnesses (p : Problem) (s : Branch) (nodes : List Nat) (maxNodes : Nat) :
    Option (Transition p s) :=
  s.labels.attach.findSome? fun ⟨(x,c),h⟩ =>
    if s.expanded.contains (x,c) then none
    else match c with
    | .some r body =>
      if nodes.any (fun y => s.edge (r,false) x y && s.known y body) then none
      else some (deterministic (s.allocate x r body (.some r body) 1 false)
        fun ⟨i,nom,hr,hc,hrc,ht,env,hs⟩ => by
          obtain ⟨y,hy⟩ := hs.1 x (.some r body) h
          obtain ⟨env',hh⟩ := Branch.allocate_sound hs (mark := .some r body) 1 false [y] rfl
            (by simp) (by simpa) (Branch.label_support h)
          exact ⟨i,nom,hr,hc,hrc,ht,env',hh⟩)
    | .min (n + 1) r body =>
      if n + 1 > maxNodes then none else
      some (deterministic (s.allocate x r body (.min (n+1) r body) (n+1) true)
        fun ⟨i,nom,hr,hc,hrc,ht,env,hs⟩ => by
          obtain ⟨values,hln,hnd,hq⟩ := hs.1 x (.min (n+1) r body) h
          obtain ⟨env',hh⟩ := Branch.allocate_sound hs (mark := .min (n+1) r body)
            (n+1) true values hln (fun _ => hnd) hq (Branch.label_support h)
          exact ⟨i,nom,hr,hc,hrc,ht,env',hh⟩)
    | _ => none

def next (p : Problem) (s : Branch) (maxNodes : Nat) : Option (Transition p s) :=
  let nodes := s.nodes
  inequalityClash p s <|> labelClash p s <|> nominalMerge p s <|> selfSteps p s <|>
    roleCharSteps p s nodes <|> localLabels p s nodes <|>
    hierarchy p s nodes <|> chains p s nodes <|> deterministicGCI p s nodes <|>
    disjunctions p s <|> upperBounds p s <|> witnesses p s nodes maxNodes <|>
    qualifiers p s nodes <|> undecidedGCI p s nodes

end Sabrina.Graded
