import Logic.FOL.Sexp

/-!
A declarative grammar for tokenized S-expressions, and a proof that the
stack parser recognizes each derivation. Both identifier and quoted tokens
produce atoms, as in the existing parser. This says nothing about the
character lexer or ISO CLIF semantics.
-/
namespace Logic.FOL

mutual
inductive Emits : Sexp → List Token → Prop where
  | ident (s : String) : Emits (.atom s) [.ident s]
  | quoted (s : String) : Emits (.atom s) [.quoted s]
  | list {trees : List Sexp} {ts : List Token} :
      EmitsMany trees ts → Emits (.list trees) ([.openP] ++ ts ++ [.closeP])

inductive EmitsMany : List Sexp → List Token → Prop where
  | nil : EmitsMany [] []
  | cons {tree : Sexp} {trees : List Sexp} {ts us : List Token} :
      Emits tree ts → EmitsMany trees us → EmitsMany (tree :: trees) (ts ++ us)
end

mutual
theorem emits_go {tree : Sexp} {ts : List Token} (h : Emits tree ts)
    (rest : List Token) (stack : List (List Sexp)) (acc : List Sexp) :
    sexpFromTokens.go (ts ++ rest) stack acc =
      sexpFromTokens.go rest stack (tree :: acc) := by
  cases h with
  | ident s => rfl
  | quoted s => rfl
  | @list trees ts h =>
    change sexpFromTokens.go (ts ++ [.closeP] ++ rest) (acc :: stack) [] =
      sexpFromTokens.go rest stack (.list trees :: acc)
    rw [List.append_assoc]
    simp only [List.singleton_append]
    rw [emitsMany_go h (.closeP :: rest) (acc :: stack) []]
    simp only [List.append_nil, sexpFromTokens.go.eq_4, List.reverse_reverse]

theorem emitsMany_go {trees : List Sexp} {ts : List Token} (h : EmitsMany trees ts)
    (rest : List Token) (stack : List (List Sexp)) (acc : List Sexp) :
    sexpFromTokens.go (ts ++ rest) stack acc =
      sexpFromTokens.go rest stack (trees.reverse ++ acc) := by
  cases h with
  | nil => rfl
  | cons first tail =>
    simp only [List.append_assoc]
    rw [emits_go first _ stack acc]
    rw [emitsMany_go tail rest stack _]
    simp [List.reverse_cons, List.append_assoc]
end

theorem emits_parses {tree : Sexp} {ts : List Token} (h : Emits tree ts) :
    sexpFromTokens ts = some [tree] := by
  have hp := emits_go h [] [] []
  simpa [sexpFromTokens, sexpFromTokens.go] using hp

theorem emitsMany_parses {trees : List Sexp} {ts : List Token} (h : EmitsMany trees ts) :
    sexpFromTokens ts = some trees := by
  have hp := emitsMany_go h [] [] []
  simpa [sexpFromTokens, sexpFromTokens.go] using hp

/-- Fuel-bounded serialization of a tree to tokens. Atom spelling is preserved;
the lexer distinction between quoted and identifier atoms is not reconstructed. -/
def serialize : Nat → Sexp → Option (List Token)
  | 0, _ => none
  | _+1, .atom s => some [.ident s]
  | n+1, .list trees => do
      let chunks ← trees.mapM (serialize n)
      pure ([.openP] ++ chunks.flatten ++ [.closeP])

theorem mapM_emitsMany {f : Sexp → Option (List Token)}
    (hf : ∀ t ts, f t = some ts → Emits t ts)
    (trees : List Sexp) (chunks : List (List Token))
    (h : trees.mapM f = some chunks) : EmitsMany trees chunks.flatten := by
  induction trees generalizing chunks with
  | nil =>
    simp [List.mapM_nil] at h
    subst chunks
    exact .nil
  | cons tree trees ih =>
    cases he : f tree with
    | none => simp [List.mapM_cons, he] at h
    | some tokens =>
      cases ht : trees.mapM f with
      | none => simp [List.mapM_cons, he, ht] at h
      | some rest =>
        simp [List.mapM_cons, he, ht] at h
        subst chunks
        exact .cons (hf tree tokens he) (ih rest ht)

theorem serialize_emits (fuel : Nat) (tree : Sexp) (ts : List Token)
    (h : serialize fuel tree = some ts) : Emits tree ts := by
  induction fuel generalizing tree ts with
  | zero => simp [serialize] at h
  | succ n ih =>
    cases tree with
    | atom s =>
      simp [serialize] at h
      subst ts
      exact .ident s
    | list trees =>
      cases hs : trees.mapM (serialize n) with
      | none => simp [serialize, hs] at h
      | some chunks =>
        simp [serialize, hs] at h
        subst ts
        exact .list (mapM_emitsMany (fun t us hu => ih t us hu) trees chunks hs)

/-- Every successful serialization is parsed back to its original tree. -/
theorem serialize_parse (fuel : Nat) (tree : Sexp) (ts : List Token)
    (h : serialize fuel tree = some ts) : sexpFromTokens ts = some [tree] :=
  emits_parses (serialize_emits fuel tree ts h)

/-- The existing checked lexer followed by the S-expression stack parser. -/
def parseChecked (input : String) : Option (List Sexp) := do
  let ts ← (tokenizeChecked input).toOption
  sexpFromTokens ts

/-- This bridge exposes the remaining lexer premise explicitly. -/
theorem parseChecked_of_tokens (input : String) (ts : List Token) (trees : List Sexp)
    (hlex : tokenizeChecked input = .ok ts) (hparse : sexpFromTokens ts = some trees) :
    parseChecked input = some trees := by
  unfold parseChecked
  rw [hlex]
  exact hparse

end Logic.FOL
