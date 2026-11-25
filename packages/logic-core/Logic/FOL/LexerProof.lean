import Logic.FOL.Lexer

/-! Properties of the checked character lexer. These statements describe the
implemented lexical state machine; they do not prove the machine conforms to
every CLIF lexical rule. -/
namespace Logic.FOL

def validLexChar (st : LexState) (c : Char) : Bool :=
  match st.mode with
  | .quote .. | .comment => true
  | _ => isSpace c || isIdentChar c || c == '(' || c == ')' ||
         c == ';' || c == '\'' || c == '"'

def checkedLexStep (c : Char) (st : LexState) : Except String (ForInStep LexState) :=
  if !validLexChar st c then .error s!"unsupported character: {c}"
  else .ok (.yield (lexStep st c))

def checkedLexWalk (cs : List Char) (st : LexState) : Except String LexState :=
  forIn cs st checkedLexStep

def checkedLexFinish (res : Except String LexState) : Except String (List Token) := do
  let st ← res
  match st.mode with
  | .quote .. => .error "unterminated quoted string"
  | _ => .ok (flush st).toks.reverse

theorem tokenizeChecked_is_walk (input : String) :
    tokenizeChecked input =
      checkedLexFinish (checkedLexWalk input.toList { toks := [], mode := .none }) := by
  rfl

theorem checkedWalk_agrees_fold (cs : List Char) (st : LexState) (result : LexState)
    (h : checkedLexWalk cs st = .ok result) :
    cs.foldl lexStep st = result := by
  induction cs generalizing st with
  | nil =>
    change Except.ok st = Except.ok result at h
    exact Except.ok.inj h
  | cons c cs ih =>
    cases hv : validLexChar st c with
    | false =>
      simp [checkedLexWalk, List.forIn_cons, checkedLexStep, hv] at h
      change Except.error _ = Except.ok result at h
      cases h
    | true =>
      simp [checkedLexWalk, List.forIn_cons, checkedLexStep, hv] at h
      exact ih (lexStep st c) h


/-- Scanning composes across character-list chunks without resetting the
state, including when a chunk ends inside a quoted token. -/
theorem checkedWalk_append (xs ys : List Char) (st : LexState) :
    checkedLexWalk (xs ++ ys) st =
      (checkedLexWalk xs st).bind (checkedLexWalk ys) := by
  induction xs generalizing st with
  | nil => rfl
  | cons c cs ih =>
    cases hv : validLexChar st c with
    | false =>
      simp only [List.cons_append, checkedLexWalk, List.forIn_cons, checkedLexStep, hv]
      rfl
    | true =>
      simp only [List.cons_append, checkedLexWalk, List.forIn_cons, checkedLexStep, hv]
      exact ih (lexStep st c)


/-- Declarative successful runs of the checked lexer, character by character.
The state includes an unfinished token and thus permits arbitrary chunking. -/
inductive CheckedLexRun : List Char → LexState → LexState → Prop where
  | nil (st : LexState) : CheckedLexRun [] st st
  | cons {c : Char} {cs : List Char} {start finish : LexState} :
      validLexChar start c = true →
      CheckedLexRun cs (lexStep start c) finish →
      CheckedLexRun (c :: cs) start finish

theorem checkedWalk_of_run {cs : List Char} {start finish : LexState}
    (h : CheckedLexRun cs start finish) : checkedLexWalk cs start = .ok finish := by
  induction h with
  | nil st => rfl
  | @cons c cs start finish hv run ih =>
    simp only [checkedLexWalk, List.forIn_cons, checkedLexStep, hv]
    exact ih

theorem run_of_checkedWalk (cs : List Char) (start finish : LexState)
    (h : checkedLexWalk cs start = .ok finish) : CheckedLexRun cs start finish := by
  induction cs generalizing start with
  | nil =>
    change Except.ok start = Except.ok finish at h
    cases h
    exact .nil _
  | cons c cs ih =>
    cases hv : validLexChar start c with
    | false =>
      simp [checkedLexWalk, List.forIn_cons, checkedLexStep, hv] at h
      change Except.error _ = Except.ok finish at h
      cases h
    | true =>
      simp [checkedLexWalk, List.forIn_cons, checkedLexStep, hv] at h
      exact .cons hv (ih _ h)

/-- The executable scan succeeds exactly when the declarative run exists. -/
theorem checkedWalk_iff_run (cs : List Char) (start finish : LexState) :
    checkedLexWalk cs start = .ok finish ↔ CheckedLexRun cs start finish :=
  ⟨run_of_checkedWalk cs start finish, checkedWalk_of_run⟩



/-- Add previously emitted tokens behind the current reversed token buffer. -/
def lexFrame (st : LexState) (suffix : List Token) : LexState :=
  { st with toks := st.toks ++ suffix }

theorem validLexChar_frame (st : LexState) (suffix : List Token) (c : Char) :
    validLexChar (lexFrame st suffix) c = validLexChar st c := by
  cases st with
  | mk tokens mode => cases mode <;> rfl


theorem lexPunct_frame (st : LexState) (suffix : List Token) (c : Char) :
    lexStep.lexPunct (lexFrame st suffix) c = lexFrame (lexStep.lexPunct st c) suffix := by
  cases h0 : isSpace c <;> cases h1 : c == '(' <;> cases h2 : c == ')' <;>
    cases h3 : c == ';' <;> cases h4 : c == '\'' || c == '"' <;>
    cases h5 : isIdentChar c <;>
    simp [lexStep.lexPunct, lexFrame, h0, h1, h2, h3, h4, h5]

theorem lexStep_frame (st : LexState) (suffix : List Token) (c : Char) :
    lexStep (lexFrame st suffix) c = lexFrame (lexStep st c) suffix := by
  cases st with
  | mk tokens mode =>
    cases mode with
    | none =>
      exact lexPunct_frame ⟨tokens, .none⟩ suffix c
    | ident buf =>
      cases hi : isIdentChar c with
      | false =>
        simpa [lexStep, lexFrame, flush, hi] using
          lexPunct_frame ⟨Token.ident (String.ofList buf.reverse) :: tokens, .none⟩ suffix c
      | true => simp [lexStep, lexFrame, hi]
    | quote q escaped buf =>
      cases escaped <;> cases hb : c == '\\' <;> cases hq : c == q <;>
        simp [lexStep, lexFrame, hb, hq]
    | comment =>
      cases hn : c == '\n' <;> simp [lexStep, lexFrame, hn]


/-- A scan remains valid when earlier emitted tokens are appended to its
reversed output buffer. -/
theorem checkedRun_frame {cs : List Char} {start finish : LexState}
    (h : CheckedLexRun cs start finish) (suffix : List Token) :
    CheckedLexRun cs (lexFrame start suffix) (lexFrame finish suffix) := by
  induction h with
  | nil st => exact .nil _
  | @cons c cs start finish hv run ih =>
    apply CheckedLexRun.cons
    · simpa only [validLexChar_frame] using hv
    · rw [lexStep_frame]
      exact ih

/-- Successful scans preserve an arbitrary earlier output buffer. -/
theorem checkedWalk_frame (cs : List Char) (start finish : LexState)
    (suffix : List Token) (h : checkedLexWalk cs start = .ok finish) :
    checkedLexWalk cs (lexFrame start suffix) = .ok (lexFrame finish suffix) :=
  checkedWalk_of_run (checkedRun_frame (run_of_checkedWalk cs start finish h) suffix)

/-- Successful chunk scans compose without re-scanning earlier chunks. -/
theorem checkedWalk_append_success (xs ys : List Char) (start middle finish : LexState)
    (hxs : checkedLexWalk xs start = .ok middle)
    (hys : checkedLexWalk ys middle = .ok finish) :
    checkedLexWalk (xs ++ ys) start = .ok finish := by
  rw [checkedWalk_append, hxs]
  exact hys


/-- A block ends outside any unfinished token. Its token list is reversed,
matching the scanner's internal buffer. -/
def LexBlock := List Char × List Token

def blocksChars (blocks : List LexBlock) : List Char :=
  blocks.flatMap Prod.fst

def blocksTokensRev (blocks : List LexBlock) : List Token :=
  (blocks.map Prod.snd).reverse.flatten

def blockCertified (block : LexBlock) : Prop :=
  checkedLexWalk block.1 { toks := [], mode := .none } =
    .ok { toks := block.2, mode := .none }

/-- Independently certified neutral-state blocks compose with any existing
reversed token buffer. -/
theorem certifiedBlocks_scan (blocks : List LexBlock)
    (h : ∀ b ∈ blocks, blockCertified b) (suffix : List Token) :
    checkedLexWalk (blocksChars blocks) { toks := suffix, mode := .none } =
      .ok { toks := blocksTokensRev blocks ++ suffix, mode := .none } := by
  induction blocks generalizing suffix with
  | nil => rfl
  | cons b bs ih =>
    have hb : blockCertified b := h b (by simp)
    have hs : ∀ x ∈ bs, blockCertified x := by
      intro x hx
      exact h x (by simp [hx])
    have hf := checkedWalk_frame b.1
      { toks := [], mode := .none } { toks := b.2, mode := .none } suffix hb
    have hfirst : checkedLexWalk b.1 { toks := suffix, mode := .none } =
        .ok { toks := b.2 ++ suffix, mode := .none } := by
      simpa [lexFrame] using hf
    have hrest := ih hs (b.2 ++ suffix)
    change checkedLexWalk (b.1 ++ blocksChars bs) { toks := suffix, mode := .none } =
      .ok { toks := blocksTokensRev (b :: bs) ++ suffix, mode := .none }
    rw [checkedWalk_append, hfirst]
    change checkedLexWalk (blocksChars bs) { toks := b.2 ++ suffix, mode := .none } = _
    have hrev : blocksTokensRev (b :: bs) = blocksTokensRev bs ++ b.2 := by
      change (b.2 :: bs.map Prod.snd).reverse.flatten =
        (bs.map Prod.snd).reverse.flatten ++ b.2
      rw [List.reverse_cons, List.flatten_append]
      simp
    rw [hrev, List.append_assoc]
    exact hrest

/-- Certified blocks yield the exact checked lexer output for the string
constructed from their characters. -/
theorem tokenizeChecked_certifiedBlocks (blocks : List LexBlock)
    (h : ∀ b ∈ blocks, blockCertified b) :
    tokenizeChecked (String.ofList (blocksChars blocks)) =
      .ok (blocksTokensRev blocks).reverse := by
  rw [tokenizeChecked_is_walk, String.toList_ofList]
  have hs := certifiedBlocks_scan blocks h []
  simp only [List.append_nil] at hs
  rw [hs]
  rfl

/-- A declarative run and the final-state check certify the checked lexer. -/
theorem tokenizeChecked_of_run (input : String) (finish : LexState) (tokens : List Token)
    (hrun : CheckedLexRun input.toList { toks := [], mode := .none } finish)
    (hfinish : checkedLexFinish (.ok finish) = .ok tokens) :
    tokenizeChecked input = .ok tokens := by
  rw [tokenizeChecked_is_walk, checkedWalk_of_run hrun]
  exact hfinish

/-- A successful checked lexing produces exactly the unchecked state-machine
tokens. The checked lexer may reject inputs that the unchecked lexer ignores. -/
theorem tokenizeChecked_agrees (input : String) (tokens : List Token)
    (h : tokenizeChecked input = .ok tokens) :
    tokenize input = tokens := by
  rw [tokenizeChecked_is_walk] at h
  cases hw : checkedLexWalk input.toList { toks := [], mode := .none } with
  | error e =>
    rw [hw] at h
    change Except.error e = Except.ok tokens at h
    cases h
  | ok result =>
    rw [hw] at h
    have hf := checkedWalk_agrees_fold input.toList { toks := [], mode := .none } result hw
    unfold tokenize
    rw [hf]
    change (match result.mode with
      | .quote .. => Except.error "unterminated quoted string"
      | _ => Except.ok (flush result).toks.reverse) = Except.ok tokens at h
    cases hm : result.mode with
    | quote q escaped buf => rw [hm] at h; cases h
    | none => rw [hm] at h; exact Except.ok.inj h
    | ident buf => rw [hm] at h; exact Except.ok.inj h
    | comment => rw [hm] at h; exact Except.ok.inj h

end Logic.FOL
