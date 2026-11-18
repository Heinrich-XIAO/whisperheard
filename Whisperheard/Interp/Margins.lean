import Whisperheard.Interp.Whisper

/-!
# Margins, ties, and composition

* **Head 1** inside the window has a unique maximum with margin exactly `4`;
  past the window **every** key scores `0` — a total tie, resolved by the
  first-argmax convention (to position `0`). This is the *only* place in
  the whole network where the tie-breaking convention is consulted.
* **Head 2** always has a unique maximum (`head2_unique`); the margin can be
  as small as `1` (`head2_margin_tight`).
* **Logits**: the winning token leads every other token by exactly `5`.
* **Composition**: head 2 composes with head 1 *only* through its keys
  (K-composition). Its queries and values ignore head 1's output entirely
  (no Q- or V-composition), and the unembedding ignores it too.
-/

namespace Whisperheard
open Circuits

variable {x : Nat → Nat} (hx : Valid x)
include hx

theorem score1_whisper (i j : Nat) :
    whisper.h1.score whisper.d (whisper.resid0 x) i j = if i < 8 ∧ i = j + 1 then 4 else 0 :=
  whisper_spec.score1_eq hx i j

theorem head1_margin (i : Nat) (hi1 : 1 ≤ i) (hi : i < 8) (k : Nat)
    (hne : k ≠ i - 1) :
    whisper.h1.score whisper.d (whisper.resid0 x) i k + 4 =
      whisper.h1.score whisper.d (whisper.resid0 x) i (i - 1) := by
  rw [score1_whisper hx, score1_whisper hx, ite_eq_right (by omega), ite_eq_left (by omega)]; rfl

theorem head1_total_tie (i : Nat) (hi : 8 ≤ i) (k : Nat) :
    whisper.h1.score whisper.d (whisper.resid0 x) i k = 0 := by
  rw [score1_whisper hx, ite_eq_right (by omega)]

theorem score2_whisper (i j : Nat) :
    whisper.h2.score whisper.d (whisper.resid1 x) i j = score2Form 8 10 Circuits.w x i j :=
  whisper_spec.score2_eq hx (by decide) i j

/-- **Head 2 never ties**: the attended key strictly beats every other key. -/
theorem head2_unique (i k : Nat) (hk : k ≤ i) (hne : k ≠ target 8 x i) :
    whisper.h2.score whisper.d (whisper.resid1 x) i k <
      whisper.h2.score whisper.d (whisper.resid1 x) i (target 8 x i) := by
  rw [score2_whisper hx, score2_whisper hx]
  exact score2_lt_target whisper_lawHyp (by decide) x i k hk hne

omit hx in
/-- …but the gap can be as small as `1`: two adjacent matches. -/
theorem head2_margin_tight :
    let x := stream [0, 0, 0]
    target 8 x 2 = 2 ∧
    whisper.h2.score whisper.d (whisper.resid1 x) 2 2 -
      whisper.h2.score whisper.d (whisper.resid1 x) 2 1 = 1 := by
  have hv : Valid (stream [0, 0, 0]) := by
    intro k; unfold stream; rw [List.getD_eq_getElem?_getD]
    cases h : [0, 0, 0][k]? <;> simp_all; have := List.mem_of_getElem? h; simp at this; omega
  simp only
  rw [score2_whisper hv, score2_whisper hv]
  decide

/-- **Logit margin**: the predicted token leads every other token by exactly `5`. -/
theorem logit_margin (i t : Nat) (ht : t < 4) (hne : t ≠ whisper.predict x i) :
    whisper.logits x i t + 5 = whisper.logits x i (whisper.predict x i) := by
  rw [predict_whisper hx] at hne ⊢
  rw [logits_whisper hx i t ht, logits_whisper hx i _ (hx _), ite_eq_right hne, ite_eq_left rfl]; rfl

/-! ## Composition -/

omit hx in
/-- Head 2 reads head 1's output through its **keys** (K-composition)… -/
theorem k_composition : ∀ t, t < 4 → qk2 (T t) (S t) = 10 := by decide +kernel

omit hx in
/-- …but not through its **queries** (no Q-composition)… -/
theorem no_q_composition : ∀ s, s < 4 → (∀ t, t < 4 → qk2 (S s) (T t) = 0) ∧
    (∀ p, p < 8 → qk2 (S s) (P p) = 0) ∧ (∀ s', s' < 4 → qk2 (S s) (S s') = 0) := by
  decide +kernel

omit hx in
/-- …nor through its **values** (no V-composition)… -/
theorem no_v_composition : ∀ s, s < 4 → ∀ k, k < 20 → ov2 (S s) k = 0 := ov2_S

omit hx in
/-- …and the logits do not read head 1's output, the token embedding, or the
position embedding: the only path to the logits is through head 2's OV. -/
theorem only_head2_path : ∀ t, t < 4 →
    (∀ t', t' < 4 → unembed t (T t') = 0) ∧ (∀ p, p < 8 → unembed t (P p) = 0) ∧
    (∀ s, s < 4 → unembed t (S s) = 0) := by decide +kernel

end Whisperheard
