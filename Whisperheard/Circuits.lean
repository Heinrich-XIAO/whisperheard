import Whisperheard.Weights

/-!
# Circuit tables, read off the raw weights

Everything here is a kernel-checked computation on the dense raw weights
(`decide +kernel`); none of it uses the hidden basis.

The residual stream is spanned by four families of vectors, all computable
from the weights alone:

* `T t`  — token embedding of token `t`           (`WE` column)
* `P p`  — positional embedding of position `p`   (`WP` column)
* `S t`  — what head 1 writes when it attends to a position holding `t`
           (`OV₁ (T t)`)
* `O t`  — what head 2 writes when it attends to a position holding `t`
           (`OV₂ (T t)`)

The tables below give every interaction between these families: each head's
QK form on every pair, each head's OV map on every family, and the
unembedding on every family. Together with linearity this determines the
whole network (`Whisperheard.Interp.Mechanism`).
-/

namespace Whisperheard.Circuits
open Whisperheard

abbrev d : Nat := 20
def T (t : Nat) : Vec := whisper.tok t
def P (p : Nat) : Vec := whisper.pos p
def S (t : Nat) : Vec := whisper.h1.ov d (T t)
def O (t : Nat) : Vec := whisper.h2.ov d (T t)
def qk1 (a b : Vec) : Int := whisper.h1.qk d a b
def qk2 (a b : Vec) : Int := whisper.h2.qk d a b
def ov1 (a : Vec) : Vec := whisper.h1.ov d a
def ov2 (a : Vec) : Vec := whisper.h2.ov d a
/-- Logit of token `t` read from residual vector `a`. -/
def unembed (t : Nat) (a : Vec) : Int := dot d (row whisper.WU t) a

/-- The positional key weight of head 2 (inside the window). -/
def w (p : Nat) : Int := if p = 0 then -10 else p

/-! ## Head 1: a pure-position QK circuit -/

theorem qk1_TT : ∀ t, t < 4 → ∀ t', t' < 4 → qk1 (T t) (T t') = 0 := by decide +kernel
theorem qk1_TP : ∀ t, t < 4 → ∀ p, p < 8 → qk1 (T t) (P p) = 0 := by decide +kernel
theorem qk1_PT : ∀ p, p < 8 → ∀ t, t < 4 → qk1 (P p) (T t) = 0 := by decide +kernel
/-- Position `p` scores `4` on position `p - 1` and `0` everywhere else. -/
theorem qk1_PP : ∀ p, p < 8 → ∀ p', p' < 8 → qk1 (P p) (P p') = if p = p' + 1 then 4 else 0 := by
  decide +kernel

/-! ## Head 1 OV: copies the token, ignores the position -/

theorem ov1_P : ∀ p, p < 8 → ∀ k, k < d → ov1 (P p) k = 0 := by decide +kernel

/-! ## Head 2 QK: match current token against head-1 output, plus a positional ramp -/

theorem qk2_TT : ∀ t, t < 4 → ∀ t', t' < 4 → qk2 (T t) (T t') = 0 := by decide +kernel
theorem qk2_TP : ∀ t, t < 4 → ∀ p, p < 8 → qk2 (T t) (P p) = w p := by decide +kernel
theorem qk2_TS : ∀ t, t < 4 → ∀ s, s < 4 → qk2 (T t) (S s) = if t = s then 10 else 0 := by
  decide +kernel
theorem qk2_PT : ∀ p, p < 8 → ∀ t, t < 4 → qk2 (P p) (T t) = 0 := by decide +kernel
theorem qk2_PP : ∀ p, p < 8 → ∀ p', p' < 8 → qk2 (P p) (P p') = 0 := by decide +kernel
theorem qk2_PS : ∀ p, p < 8 → ∀ s, s < 4 → qk2 (P p) (S s) = 0 := by decide +kernel
theorem qk2_ST : ∀ s, s < 4 → ∀ t, t < 4 → qk2 (S s) (T t) = 0 := by decide +kernel
theorem qk2_SP : ∀ s, s < 4 → ∀ p, p < 8 → qk2 (S s) (P p) = 0 := by decide +kernel
theorem qk2_SS : ∀ s, s < 4 → ∀ s', s' < 4 → qk2 (S s) (S s') = 0 := by decide +kernel

/-! ## Head 2 OV: copies the token only -/

theorem ov2_P : ∀ p, p < 8 → ∀ k, k < d → ov2 (P p) k = 0 := by decide +kernel
theorem ov2_S : ∀ s, s < 4 → ∀ k, k < d → ov2 (S s) k = 0 := by decide +kernel

/-! ## Unembedding: reads only head 2's output -/

theorem U_T : ∀ t, t < 4 → ∀ t', t' < 4 → unembed t (T t') = 0 := by decide +kernel
theorem U_P : ∀ t, t < 4 → ∀ p, p < 8 → unembed t (P p) = 0 := by decide +kernel
theorem U_S : ∀ t, t < 4 → ∀ s, s < 4 → unembed t (S s) = 0 := by decide +kernel
theorem U_O : ∀ t, t < 4 → ∀ s, s < 4 → unembed t (O s) = if t = s then 5 else 0 := by
  decide +kernel

/-! ## Out-of-range embeddings are zero -/

theorem WP_rows : ∀ r ∈ Weights.WP, r.length = 8 := by decide

theorem P_out (p : Nat) (hp : 8 ≤ p) : P p = zeroV := by
  funext k
  show ofRows Weights.WP k p = 0
  apply ofRows_out_col
  intro r hr; rw [WP_rows r hr]; exact hp

end Whisperheard.Circuits
