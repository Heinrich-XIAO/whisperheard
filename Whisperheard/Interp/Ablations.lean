import Whisperheard.Interp.Basis
import Whisperheard.Interp.Whisper

/-!
# Ablations: which parts matter, and how much

Every ablation is a **weight edit** of the real network, followed by fresh
kernel-checked circuit tables for the edited network and the generic
mechanism theorem (`Spec.predict_formula`). Edits that touch a single
feature direction use the recovered basis: `delDirs lo hi` is the
projector that deletes basis directions `lo, …, hi-1`, so `WK · delDirs`
is "the same key matrix, but blind to those directions".

| edit                                   | result                                        |
|----------------------------------------|-----------------------------------------------|
| head 1 output zeroed                   | echoes the current token (`noHead1_law`)      |
| head 2 output zeroed                   | constant: always predicts `0` (`noHead2_law`) |
| head 2 blind to position (no ramp)     | breaks recency (`noRamp_breaks`)              |
| head 2 blind to position 0 only        | **no change at all** (`noSuppress_same`)      |
| match strength 10 replaced by `c`      | works **iff `c ≥ 6`** (`frontier`)            |
-/

namespace Whisperheard.Interp
open Whisperheard Circuits

/-- Projector deleting basis directions `lo, …, hi-1` (along the others). -/
def delDirs (lo hi : Nat) : Mat := fun r c =>
  (if r = c then 1 else 0) - sumN 20 (fun a => if lo ≤ a ∧ a < hi then B r a * Binv a c else 0)

/-- Projector keeping only basis directions `lo, …, hi-1`. -/
def keepDirs (lo hi : Nat) : Mat := fun r c =>
  sumN 20 (fun a => if lo ≤ a ∧ a < hi then B r a * Binv a c else 0)

theorem stream_valid (l : List Nat) (h : ∀ a ∈ l, a < 4) : Valid (stream l) := by
  intro k
  unfold stream
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[k]? with
  | none => simp
  | some a => simp only [Option.getD_some]; exact h a (List.mem_of_getElem? hk)

/-! ## Ablation 1: delete head 1's output -/

def noHead1 : Model := { whisper with h1 := { whisper.h1 with WO := fun _ _ => 0 } }

theorem noHead1_spec : Spec noHead1 4 0 5 Circuits.w where
  pos_out := P_out
  qk1_TT := qk1_TT
  qk1_TP := qk1_TP
  qk1_PT := qk1_PT
  qk1_PP := qk1_PP
  ov1_P := by decide +kernel
  qk2_TT := qk2_TT
  qk2_TP := qk2_TP
  qk2_TS := by decide +kernel
  qk2_PT := qk2_PT
  qk2_PP := qk2_PP
  qk2_PS := by decide +kernel
  qk2_ST := by decide +kernel
  qk2_SP := by decide +kernel
  qk2_SS := by decide +kernel
  ov2_P := ov2_P
  ov2_S := by decide +kernel
  U_T := U_T
  U_P := U_P
  U_S := by decide +kernel
  U_O := U_O

/-- **Without head 1 the network only echoes**: it outputs the current token
(and past the window, token 7). Induction is gone. -/
theorem noHead1_law {x : Nat → Nat} (hx : Valid x) (i : Nat) :
    noHead1.predict x i = x (min i 7) := by
  rw [noHead1_spec.predict_formula hx (by decide) (by decide) i]
  congr 1
  by_cases hi0 : i = 0
  · subst hi0; rfl
  apply argmaxUpTo_eq_of_strict _ _ _ (by omega)
  intro k hk hne
  show score2Form 8 0 Circuits.w x i k < score2Form 8 0 Circuits.w x i (min i 7)
  unfold score2Form Circuits.w
  rw [ite_eq_left (by omega : min i 7 < 8), ite_eq_right (by omega : ¬ min i 7 = 0)]
  by_cases hk8 : k < 8
  · rw [ite_eq_left hk8]; split <;> split <;> omega
  · rw [ite_eq_right hk8]; split <;> split <;> omega

/-- Head 1 is necessary: a concrete input where the ablated network errs. -/
theorem noHead1_breaks :
    noHead1.predict (stream [0, 1, 0]) 2 ≠ whisper.predict (stream [0, 1, 0]) 2 := by
  have hv := stream_valid [0, 1, 0] (by decide)
  rw [noHead1_law hv, predict_whisper hv]; decide

/-! ## Ablation 2: delete head 2's output -/

def noHead2 : Model := { whisper with h2 := { whisper.h2 with WO := fun _ _ => 0 } }

theorem noHead2_spec : Spec noHead2 4 10 0 Circuits.w where
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
  ov2_P := by decide +kernel
  ov2_S := by decide +kernel
  U_T := U_T
  U_P := U_P
  U_S := U_S
  U_O := by decide +kernel

/-- **Without head 2 the network is constant.** The direct path and the
head-1 path contribute exactly nothing to the logits. -/
theorem noHead2_law {x : Nat → Nat} (hx : Valid x) (i : Nat) : noHead2.predict x i = 0 :=
  noHead2_spec.predict_of_cU_zero hx (by decide) rfl i

/-! ## Ablation 3: blind head 2's keys to position (delete the ramp) -/

def noRamp : Model :=
  { whisper with h2 := { whisper.h2 with WK := mmul whisper.h2.WK (delDirs 4 12) 20 } }

theorem noRamp_spec : Spec noRamp 4 10 5 (fun _ => 0) where
  pos_out := P_out
  qk1_TT := qk1_TT
  qk1_TP := qk1_TP
  qk1_PT := qk1_PT
  qk1_PP := qk1_PP
  ov1_P := ov1_P
  qk2_TT := by decide +kernel
  qk2_TP := by decide +kernel
  qk2_TS := by decide +kernel
  qk2_PT := by decide +kernel
  qk2_PP := by decide +kernel
  qk2_PS := by decide +kernel
  qk2_ST := by decide +kernel
  qk2_SP := by decide +kernel
  qk2_SS := by decide +kernel
  ov2_P := ov2_P
  ov2_S := ov2_S
  U_T := U_T
  U_P := U_P
  U_S := U_S
  U_O := U_O

/-- **The ramp is what makes head 2 pick the *latest* occurrence.** Without it
every match ties and the first one wins. -/
theorem noRamp_breaks :
    noRamp.predict (stream [0, 1, 0, 2, 0]) 4 = 0 ∧ whisper.predict (stream [0, 1, 0, 2, 0]) 4 = 2 := by
  have hv := stream_valid [0, 1, 0, 2, 0] (by decide)
  rw [noRamp_spec.predict_formula hv (by decide) (by decide), predict_whisper hv]
  decide

/-! ## Ablation 4: blind head 2's keys to position 0 only -/

def noSuppress : Model :=
  { whisper with h2 := { whisper.h2 with WK := mmul whisper.h2.WK (delDirs 4 5) 20 } }

/-- The ramp of the edited network: position 0 now reads `0` instead of `-10`. -/
def wNoSuppress (p : Nat) : Int := if p = 0 then 0 else p

theorem noSuppress_spec : Spec noSuppress 4 10 5 wNoSuppress where
  pos_out := P_out
  qk1_TT := qk1_TT
  qk1_TP := qk1_TP
  qk1_PT := qk1_PT
  qk1_PP := qk1_PP
  ov1_P := ov1_P
  qk2_TT := by decide +kernel
  qk2_TP := by decide +kernel
  qk2_TS := by decide +kernel
  qk2_PT := by decide +kernel
  qk2_PP := by decide +kernel
  qk2_PS := by decide +kernel
  qk2_ST := by decide +kernel
  qk2_SP := by decide +kernel
  qk2_SS := by decide +kernel
  ov2_P := ov2_P
  ov2_S := ov2_S
  U_T := U_T
  U_P := U_P
  U_S := U_S
  U_O := U_O

theorem noSuppress_lawHyp : LawHyp 8 10 wNoSuppress where
  two_le := by decide
  w1_pos := by decide
  w0_lt := by decide
  mono := by
    intro a b ha hab hb; unfold wNoSuppress
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
  match_wins := by decide

/-- **The `-10` that head 2 puts on position 0 is dead weight.** Deleting it
changes attention scores but not a single prediction, on any input. (Why:
whenever position 0 could match, position 1 is a genuine match that
outscores it.) -/
theorem noSuppress_same {x : Nat → Nat} (hx : Valid x) (i : Nat) :
    noSuppress.predict x i = whisper.predict x i := by
  rw [noSuppress_spec.predict_law noSuppress_lawHyp (by decide) (by decide) hx, predict_whisper hx]
  rfl

/-! ## The frontier: how strong must the match bonus be? -/

/-- The part of head 2's key matrix that reads the head-1 directions `S`,
per unit of match strength. -/
def unitS : Mat := fun r k => mmul whisper.h2.WK (keepDirs 12 16) 20 r k / 10

theorem unitS_exact : ∀ r, r < 5 → ∀ k, k < 20 →
    10 * unitS r k = mmul whisper.h2.WK (keepDirs 12 16) 20 r k := by decide +kernel

/-- `whisper` with its match bonus `10` replaced by an arbitrary integer `c`. -/
def whisperC (c : Int) : Model :=
  { whisper with h2 := { whisper.h2 with
      WK := fun r k => mmul whisper.h2.WK (delDirs 12 16) 20 r k + c * unitS r k } }

/-- The family passes through the real network. -/
theorem whisperC_ten : ∀ r, r < 5 → ∀ k, k < 20 → (whisperC 10).h2.WK r k = whisper.h2.WK r k := by
  decide +kernel

/-- Scores are affine in the key matrix. -/
theorem qk_affine (h : Head) (A U : Mat) (c : Int) (a b : Vec) :
    ({ h with WK := fun r k => A r k + c * U r k } : Head).qk 20 a b =
      ({ h with WK := A } : Head).qk 20 a b + c * ({ h with WK := U } : Head).qk 20 a b := by
  unfold Head.qk Head.k Head.q
  simp only
  rw [← dot_smul_right, ← dot_add_right]
  congr 1; funext r
  show sumN 20 (fun k => (A r k + c * U r k) * b k) =
    sumN 20 (fun k => A r k * b k) + c * sumN 20 (fun k => U r k * b k)
  rw [← sumN_mul_left, ← sumN_add]; apply sumN_congr; intro k _; grind

def hA : Head := { whisper.h2 with WK := mmul whisper.h2.WK (delDirs 12 16) 20 }
def hU : Head := { whisper.h2 with WK := unitS }

theorem whisperC_qk (c : Int) (a b : Vec) :
    (whisperC c).h2.qk 20 a b = hA.qk 20 a b + c * hU.qk 20 a b :=
  qk_affine whisper.h2 _ _ c a b

theorem whisperC_spec (c : Int) : Spec (whisperC c) 4 c 5 Circuits.w := by
  have tT : ∀ t, t < 4 → ∀ t', t' < 4 → hA.qk 20 (T t) (T t') = 0 ∧ hU.qk 20 (T t) (T t') = 0 := by
    decide +kernel
  have tP : ∀ t, t < 4 → ∀ p, p < 8 → hA.qk 20 (T t) (P p) = Circuits.w p ∧ hU.qk 20 (T t) (P p) = 0 := by
    decide +kernel
  have tS : ∀ t, t < 4 → ∀ s, s < 4 →
      hA.qk 20 (T t) (S s) = 0 ∧ hU.qk 20 (T t) (S s) = if t = s then 1 else 0 := by decide +kernel
  have zero : ∀ u v : Vec, hA.qk 20 u v = 0 → hU.qk 20 u v = 0 → (whisperC c).h2.qk 20 u v = 0 := by
    intro u v h1 h2; rw [whisperC_qk, h1, h2]; simp
  have pT : ∀ p, p < 8 → ∀ t, t < 4 → hA.qk 20 (P p) (T t) = 0 ∧ hU.qk 20 (P p) (T t) = 0 := by
    decide +kernel
  have pP : ∀ p, p < 8 → ∀ p', p' < 8 → hA.qk 20 (P p) (P p') = 0 ∧ hU.qk 20 (P p) (P p') = 0 := by
    decide +kernel
  have pS : ∀ p, p < 8 → ∀ s, s < 4 → hA.qk 20 (P p) (S s) = 0 ∧ hU.qk 20 (P p) (S s) = 0 := by
    decide +kernel
  have sT : ∀ s, s < 4 → ∀ t, t < 4 → hA.qk 20 (S s) (T t) = 0 ∧ hU.qk 20 (S s) (T t) = 0 := by
    decide +kernel
  have sP : ∀ s, s < 4 → ∀ p, p < 8 → hA.qk 20 (S s) (P p) = 0 ∧ hU.qk 20 (S s) (P p) = 0 := by
    decide +kernel
  have sS : ∀ s, s < 4 → ∀ s', s' < 4 → hA.qk 20 (S s) (S s') = 0 ∧ hU.qk 20 (S s) (S s') = 0 := by
    decide +kernel
  exact {
    pos_out := P_out
    qk1_TT := qk1_TT
    qk1_TP := qk1_TP
    qk1_PT := qk1_PT
    qk1_PP := qk1_PP
    ov1_P := ov1_P
    qk2_TT := fun t ht t' ht' => zero _ _ (tT t ht t' ht').1 (tT t ht t' ht').2
    qk2_TP := fun t ht p hp => by
      show (whisperC c).h2.qk 20 (T t) (P p) = _
      rw [whisperC_qk, (tP t ht p hp).1, (tP t ht p hp).2]; simp
    qk2_TS := fun t ht s hs => by
      show (whisperC c).h2.qk 20 (T t) (S s) = _
      rw [whisperC_qk, (tS t ht s hs).1, (tS t ht s hs).2]; split <;> simp
    qk2_PT := fun p hp t ht => zero _ _ (pT p hp t ht).1 (pT p hp t ht).2
    qk2_PP := fun p hp p' hp' => zero _ _ (pP p hp p' hp').1 (pP p hp p' hp').2
    qk2_PS := fun p hp s hs => zero _ _ (pS p hp s hs).1 (pS p hp s hs).2
    qk2_ST := fun s hs t ht => zero _ _ (sT s hs t ht).1 (sT s hs t ht).2
    qk2_SP := fun s hs p hp => zero _ _ (sP s hs p hp).1 (sP s hs p hp).2
    qk2_SS := fun s hs s' hs' => zero _ _ (sS s hs s' hs').1 (sS s hs s' hs').2
    ov2_P := ov2_P
    ov2_S := ov2_S
    U_T := U_T
    U_P := U_P
    U_S := U_S
    U_O := U_O }

/-- **The exact frontier.** The network with match strength `c` obeys the law
of `whisper` on every input iff `c ≥ 6`. The real network uses `10`, so its
safety margin is exactly `4`. (At `c = 6` the network survives only through
first-argmax tie-breaking.) -/
theorem frontier (c : Int) :
    (∀ x : Nat → Nat, Valid x → ∀ i, (whisperC c).predict x i = x (target 8 x i)) ↔ 6 ≤ c := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hc
    have hv := stream_valid [0, 1, 2, 2, 2, 2, 2, 0] (by decide)
    have e := h _ hv 7
    rw [(whisperC_spec c).predict_formula hv (by decide) (by decide)] at e
    have ht : target 8 (stream [0, 1, 2, 2, 2, 2, 2, 0]) 7 = 1 := by decide
    rw [ht] at e
    have ha : argmaxUpTo (score2Form 8 c Circuits.w (stream [0, 1, 2, 2, 2, 2, 2, 0]) 7) 7 = 7 := by
      apply argmaxUpTo_eq_of_strict _ _ _ (by omega)
      intro k hk hne
      have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [score2Form, prevPos, stream, Circuits.w] <;> omega
    rw [show (whisperC c).N = 8 from rfl, ha] at e
    exact absurd e (by decide)
  · intro hc
    intro x hx i
    have hw : LawHyp 8 c Circuits.w :=
      { two_le := by decide
        w1_pos := by decide
        w0_lt := by decide
        mono := whisper_lawHyp.mono
        match_wins := by unfold Circuits.w; simp; omega }
    exact (whisperC_spec c).predict_law hw (by decide) (by decide) hx i

end Whisperheard.Interp
