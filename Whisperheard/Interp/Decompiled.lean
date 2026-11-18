import Whisperheard.Interp.Ablations

/-!
# The decompiled network

Reading the closed forms of `Whisperheard.Interp.Basis` back as weights gives
a sparse network written in the discovered coordinates:

  residual layout  `0..3` token · `4..11` position · `12..15` previous token ·
  `16..19` output

and every weight is a one-line formula. `decompiled_eq` proves it computes
exactly the same function as the dense raw network on every input.
-/

namespace Whisperheard.Interp
open Whisperheard

def decompiled : Model where
  V := 4
  N := 8
  d := 20
  WE := fun r t => if r = t ∧ t < 4 then 1 else 0
  WP := fun r p => if p < 8 ∧ r = 4 + p then 1 else 0
  WU := fun t r => if t < 4 ∧ r = 16 + t then 5 else 0
  h1 :=
    { dh := 8, dv := 4
      -- query: my position; key: (my position) + 1, scaled by 4
      WQ := fun a r => if a < 8 ∧ r = 4 + a then 1 else 0
      WK := fun a r => if 1 ≤ a ∧ a < 8 ∧ r = 3 + a then 4 else 0
      -- value: my token; output: write it into the previous-token slot
      WV := fun a r => if a < 4 ∧ r = a then 1 else 0
      WO := fun r a => if a < 4 ∧ r = 12 + a then 1 else 0 }
  h2 :=
    { dh := 5, dv := 4
      -- query: my token (one-hot), plus a constant 1 in coordinate 4
      WQ := fun a r => if a < 4 then (if r = a then 1 else 0) else if a = 4 ∧ r < 4 then 1 else 0
      -- key: 10 × my previous token, plus the positional ramp in coordinate 4
      WK := fun a r => if a < 4 then (if r = 12 + a then 10 else 0)
        else if a = 4 ∧ 4 ≤ r ∧ r < 12 then Circuits.w (r - 4) else 0
      -- value: my token; output: write it into the output slot
      WV := fun a r => if a < 4 ∧ r = a then 1 else 0
      WO := fun r a => if a < 4 ∧ r = 16 + a then 1 else 0 }

theorem decompiled_spec : Spec decompiled 4 10 5 Circuits.w where
  pos_out := by
    intro p hp; funext r
    have hp' : 8 ≤ p := hp
    have : ¬(p < 8 ∧ r = 4 + p) := by omega
    show (if p < 8 ∧ r = 4 + p then 1 else 0) = 0
    rw [ite_eq_right this]
  qk1_TT := by decide +kernel
  qk1_TP := by decide +kernel
  qk1_PT := by decide +kernel
  qk1_PP := by decide +kernel
  ov1_P := by decide +kernel
  qk2_TT := by decide +kernel
  qk2_TP := by decide +kernel
  qk2_TS := by decide +kernel
  qk2_PT := by decide +kernel
  qk2_PP := by decide +kernel
  qk2_PS := by decide +kernel
  qk2_ST := by decide +kernel
  qk2_SP := by decide +kernel
  qk2_SS := by decide +kernel
  ov2_P := by decide +kernel
  ov2_S := by decide +kernel
  U_T := by decide +kernel
  U_P := by decide +kernel
  U_S := by decide +kernel
  U_O := by decide +kernel

/-- **Decompilation is exact**: the sparse network and the dense raw network
agree on every input at every position. -/
theorem decompiled_eq {x : Nat → Nat} (hx : Valid x) (i : Nat) :
    decompiled.predict x i = whisper.predict x i := by
  rw [decompiled_spec.predict_law whisper_lawHyp (by decide) (by decide) hx, predict_whisper hx]
  rfl

/-- Nonzero weights of the decompiled network (every matrix, every entry). -/
def nnz (A : Mat) (rows cols : Nat) : Nat :=
  ((List.range rows).flatMap fun r => (List.range cols).filter fun c => A r c ≠ 0).length

theorem decompiled_nnz :
    nnz decompiled.WE 20 4 + nnz decompiled.WP 20 8 + nnz decompiled.WU 4 20 +
    nnz decompiled.h1.WQ 8 20 + nnz decompiled.h1.WK 8 20 + nnz decompiled.h1.WV 4 20 +
    nnz decompiled.h1.WO 20 4 + nnz decompiled.h2.WQ 5 20 + nnz decompiled.h2.WK 5 20 +
    nnz decompiled.h2.WV 4 20 + nnz decompiled.h2.WO 20 4 = 67 := by decide +kernel

/-- …versus the raw network: 962 of its 1160 weights are nonzero. -/
theorem raw_nnz :
    nnz whisper.WE 20 4 + nnz whisper.WP 20 8 + nnz whisper.WU 4 20 +
    nnz whisper.h1.WQ 8 20 + nnz whisper.h1.WK 8 20 + nnz whisper.h1.WV 4 20 +
    nnz whisper.h1.WO 20 4 + nnz whisper.h2.WQ 5 20 + nnz whisper.h2.WK 5 20 +
    nnz whisper.h2.WV 4 20 + nnz whisper.h2.WO 20 4 = 962 := by decide +kernel

end Whisperheard.Interp
