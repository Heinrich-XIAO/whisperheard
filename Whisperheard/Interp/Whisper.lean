import Whisperheard.Circuits
import Whisperheard.Interp.Law

/-!
# Everything `whisper` does

The headline results:

* `whisper_spec` — the circuit tables of the real network (from the raw
  weights, by kernel computation).
* `attn1_whisper` — head 1 attends to the previous position (inside the window).
* `logits_whisper` — exact logits: `5` on one token, `0` on the other three.
* `predict_whisper` — **the complete input–output law**, for every input
  stream and every position (inside and outside the context window).
* corollaries spelling the law out in words, causality, and equivariance
  under relabelling the vocabulary.
-/

namespace Whisperheard
open Circuits

theorem whisper_spec : Spec whisper 4 10 5 Circuits.w where
  pos_out := P_out
  qk1_TT := qk1_TT
  qk1_TP := qk1_TP
  qk1_PT := qk1_PT
  qk1_PP := qk1_PP
  ov1_P := ov1_P
  qk2_TT := qk2_TT
  qk2_TP := qk2_TP
  qk2_TS := qk2_TS
  qk2_PT := qk2_PT
  qk2_PP := qk2_PP
  qk2_PS := qk2_PS
  qk2_ST := qk2_ST
  qk2_SP := qk2_SP
  qk2_SS := qk2_SS
  ov2_P := ov2_P
  ov2_S := ov2_S
  U_T := U_T
  U_P := U_P
  U_S := U_S
  U_O := U_O

theorem whisper_lawHyp : LawHyp 8 10 Circuits.w where
  two_le := by decide
  w1_pos := by decide
  w0_lt := by decide
  mono := by intro a b ha hab hb; unfold Circuits.w; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
  match_wins := by decide

/-- A valid input: every token is in the vocabulary `{0,1,2,3}`. -/
def Valid (x : Nat → Nat) : Prop := ∀ k, x k < 4

variable {x : Nat → Nat} (hx : Valid x)
include hx

/-- **Head 1 is a previous-token head.** -/
theorem attn1_whisper (i : Nat) : whisper.attn1 x i = prevPos 8 i :=
  whisper_spec.attn1_eq hx (by decide) i

/-- **Head 2 attends to `target`.** -/
theorem attn2_whisper (i : Nat) : whisper.attn2 x i = target 8 x i :=
  whisper_spec.attn2_law whisper_lawHyp (by decide) hx i

/-- **Exact logits.** -/
theorem logits_whisper (i t : Nat) (ht : t < 4) :
    whisper.logits x i t = if t = x (target 8 x i) then 5 else 0 := by
  rw [whisper_spec.logits_eq hx (by decide) i t ht, attn2_whisper hx]

/-- **The complete law of `whisper`.** For every input stream over the
vocabulary and every position `i`, the network predicts the token at
`target 8 x i`. -/
theorem predict_whisper (i : Nat) : whisper.predict x i = x (target 8 x i) :=
  whisper_spec.predict_law whisper_lawHyp (by decide) (by decide) hx i

/-! ## The law in words -/

/-- **Induction.** Inside the window, if the current token occurred before and
its latest earlier occurrence is at `k`, the network predicts `x (k+1)`. -/
theorem predict_induction (i k : Nat) (hi : i < 8) (hk : k < i) (hm : x k = x i)
    (hlast : ∀ k', k < k' → k' < i → x k' ≠ x i) : whisper.predict x i = x (k + 1) := by
  rw [predict_whisper hx]
  unfold target; simp only
  rw [show min i (8 - 1) = i by omega]
  cases hf : findMatch x (x i) i with
  | none => have := findMatch_none x (x i) i hf (k + 1) (by omega) (by omega); simp_all
  | some j =>
    obtain ⟨h1, h2, h3, h4⟩ := findMatch_some x (x i) i j hf
    simp only [Option.getD_some]
    have : j = k + 1 := by
      rcases Nat.lt_trichotomy j (k + 1) with h | h | h
      · exact absurd hm (by have := h4 (k + 1) (by omega) (by omega); simpa using this)
      · exact h
      · exact absurd h3 (hlast (j - 1) (by omega) (by omega))
    rw [this]

/-- **Default.** Inside the window, a token never seen before is repeated. -/
theorem predict_fresh (i : Nat) (hi : i < 8) (hnew : ∀ k, k < i → x k ≠ x i) :
    whisper.predict x i = x i := by
  rw [predict_whisper hx]
  unfold target; simp only
  rw [show min i (8 - 1) = i by omega]
  cases hf : findMatch x (x i) i with
  | none => rfl
  | some j =>
    obtain ⟨h1, h2, h3, _⟩ := findMatch_some x (x i) i j hf
    exact absurd h3 (hnew (j - 1) (by omega))

/-- **Beyond the window** the network keeps doing induction, but only over the
first eight tokens: it looks up the latest occurrence of `x i` among
`x 0, …, x 6`, and otherwise outputs `x 7`. -/
theorem predict_beyond (i : Nat) (hi : 8 ≤ i) :
    whisper.predict x i = x ((findMatch x (x i) 7).getD 7) := by
  rw [predict_whisper hx]; unfold target; simp only; rw [show min i (8 - 1) = 7 by omega]

omit hx in
/-- **Causality.** The prediction at `i` depends only on `x 0, …, x i`. -/
theorem predict_causal {y : Nat → Nat} (hx : Valid x) (hy : Valid y) (i : Nat)
    (h : ∀ k, k ≤ i → x k = y k) : whisper.predict x i = whisper.predict y i := by
  rw [predict_whisper hx, predict_whisper hy]
  unfold target; simp only
  rw [h i (Nat.le_refl _), findMatch_congr x y (y i) _ (fun k hk => h k (by omega))]
  have : (findMatch y (y i) (min i (8 - 1))).getD (min i (8 - 1)) ≤ i := by
    cases hf : findMatch y (y i) (min i (8 - 1)) with
    | none => simp; omega
    | some j => have := (findMatch_some _ _ _ _ hf).2.1; simp; omega
  exact h _ this

theorem findMatch_map (σ : Nat → Nat) (hσ : ∀ a b, a < 4 → b < 4 → σ a = σ b → a = b)
    (q r : Nat) (hq : q < 4) : findMatch (σ ∘ x) (σ q) r = findMatch x q r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [findMatch, Function.comp]
    rw [ih]
    by_cases h : x r = q
    · simp [h]
    · have : σ (x r) ≠ σ q := fun e => h (hσ _ _ (hx r) hq e)
      simp [h, this]

/-- **Equivariance.** Relabelling the vocabulary by any permutation commutes
with the network. (Not at all evident from the raw weights; immediate from
the law.) -/
theorem predict_equivariant (σ : Nat → Nat) (hσ : ∀ a b, a < 4 → b < 4 → σ a = σ b → a = b)
    (hσ4 : ∀ a, a < 4 → σ a < 4) (i : Nat) :
    whisper.predict (σ ∘ x) i = σ (whisper.predict x i) := by
  have hy : Valid (σ ∘ x) := fun k => hσ4 _ (hx k)
  rw [predict_whisper hy, predict_whisper hx]
  unfold target; simp only [Function.comp]
  rw [findMatch_map hx σ hσ _ _ (hx i)]

end Whisperheard
