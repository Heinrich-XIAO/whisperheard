import Whisperheard.Circuits
import Whisperheard.Interp.BasisData
import Whisperheard.Interp.Mechanism

/-!
# The hidden basis, recovered from the weights

The twenty vectors

  `T 0..3`, `P 0..7`, `S 0..3 = OV₁ (T ·)`, `O 0..3 = OV₂ (T ·)`

(all read off the raw weights) are the columns of `B`. We prove:

* `B` is **unimodular**: an explicit integer matrix `Binv` is a two-sided
  inverse (`Binv_mul_B`, `B_mul_Binv`). So these directions are a basis of
  `ℤ²⁰`, and every residual vector has unique integer coordinates `coords`.
* In these coordinates **every circuit is sparse**, and we give each one in
  closed form *on arbitrary residual vectors* (`qk1_closed`, `qk2_closed`,
  `ov1_closed`, `ov2_closed`, `unembed_closed`). Counting nonzero entries:
  QK₁ has 7, OV₁ has 4, QK₂ has 36, OV₂ has 4, the unembedding has 4 —
  **55 integers describe the entire network.**
-/

namespace Whisperheard.Interp
open Whisperheard Circuits

/-- The `a`-th discovered direction. -/
def Bcol (a : Nat) : Vec :=
  if a < 4 then T a else if a < 12 then P (a - 4) else if a < 16 then S (a - 12) else O (a - 16)
def B : Mat := fun r a => Bcol a r
def Binv : Mat := ofRows BinvRows

theorem Binv_mul_B : ∀ a, a < 20 → ∀ b, b < 20 → mmul Binv B 20 a b = if a = b then 1 else 0 := by
  decide +kernel
theorem B_mul_Binv : ∀ r, r < 20 → ∀ c, c < 20 → mmul B Binv 20 r c = if r = c then 1 else 0 := by
  decide +kernel

/-- Coordinates of a residual vector in the discovered basis. -/
def coords (u : Vec) (a : Nat) : Int := sumN 20 (fun r => Binv a r * u r)

/-- Every residual vector is the combination of the basis with its coordinates. -/
theorem recon (u : Vec) : EqOn 20 u (fun r => sumN 20 (fun a => B r a * coords u a)) := by
  intro r hr
  show u r = sumN 20 (fun a => B r a * sumN 20 (fun s => Binv a s * u s))
  rw [show (fun a => B r a * sumN 20 (fun s => Binv a s * u s)) =
      (fun a => sumN 20 (fun s => B r a * Binv a s * u s)) by
    funext a; rw [← sumN_mul_left]; apply sumN_congr; intro s _; grind]
  rw [sumN_comm]
  rw [show (fun s => sumN 20 (fun a => B r a * Binv a s * u s)) =
      (fun s => mmul B Binv 20 r s * u s) by
    funext s; unfold mmul; rw [← sumN_mul_right]]
  rw [sumN_single 20 _ r hr (fun s hs hsr => by rw [B_mul_Binv r hr s hs, ite_eq_right (Ne.symm hsr)]; simp)]
  rw [B_mul_Binv r hr r hr]; simp

/-- Coordinates of a basis vector. -/
theorem coords_Bcol (a b : Nat) (ha : a < 20) (hb : b < 20) :
    coords (Bcol b) a = if a = b then 1 else 0 := by
  rw [← Binv_mul_B a ha b hb]; rfl

/-! ## Circuits as 20×20 matrices in the discovered basis -/

def QK1B (a b : Nat) : Int := qk1 (Bcol a) (Bcol b)
def QK2B (a b : Nat) : Int := qk2 (Bcol a) (Bcol b)
def OV1B (a b : Nat) : Int := coords (ov1 (Bcol b)) a
def OV2B (a b : Nat) : Int := coords (ov2 (Bcol b)) a
def UB (t b : Nat) : Int := unembed t (Bcol b)

/-- QK₁: position `p` attends to position `p-1` with strength 4. Nothing else. -/
theorem QK1B_eq : ∀ a, a < 20 → ∀ b, b < 20 →
    QK1B a b = if 4 ≤ b ∧ a < 12 ∧ a = b + 1 then 4 else 0 := by decide +kernel

/-- QK₂: query token `t` matches key "previous token" `t` with strength 10,
and reads the key position through the ramp `w`. Nothing else. -/
theorem QK2B_eq : ∀ a, a < 20 → ∀ b, b < 20 →
    QK2B a b = if a < 4 then (if b = a + 12 then 10 else if 4 ≤ b ∧ b < 12 then w (b - 4) else 0)
      else 0 := by decide +kernel

/-- OV₁: copies token `t` into the "previous token" slot `S t`. Nothing else. -/
theorem OV1B_eq : ∀ a, a < 20 → ∀ b, b < 20 → OV1B a b = if b < 4 ∧ a = b + 12 then 1 else 0 := by
  decide +kernel

/-- OV₂: copies token `t` into the output slot `O t`. Nothing else. -/
theorem OV2B_eq : ∀ a, a < 20 → ∀ b, b < 20 → OV2B a b = if b < 4 ∧ a = b + 16 then 1 else 0 := by
  decide +kernel

/-- Unembedding: logit `t` reads output slot `O t` with gain 5. Nothing else. -/
theorem UB_eq : ∀ t, t < 4 → ∀ b, b < 20 → UB t b = if b = t + 16 then 5 else 0 := by
  decide +kernel

/-! ## Closed forms on arbitrary residual vectors -/

/-- Bilinear expansion of a head's QK form in the basis. -/
theorem qk_expand (h : Head) (u v : Vec) :
    h.qk 20 u v = sumN 20 (fun a => sumN 20 (fun b =>
      coords u a * coords v b * h.qk 20 (Bcol a) (Bcol b))) := by
  rw [Head.qk_eqOn h 20 _ _ _ _ (recon u) (recon v)]
  unfold Head.qk Head.q Head.k
  have e1 : mulVec h.WQ 20 (fun r => sumN 20 (fun a => B r a * coords u a)) =
      fun k => sumN 20 (fun a => coords u a * mulVec h.WQ 20 (Bcol a) k) := by
    funext k; rw [mulVec_comb]; rfl
  have e2 : mulVec h.WK 20 (fun r => sumN 20 (fun a => B r a * coords v a)) =
      fun k => sumN 20 (fun a => coords v a * mulVec h.WK 20 (Bcol a) k) := by
    funext k; rw [mulVec_comb]; rfl
  rw [e1, e2, dot_comb]

theorem ov_expand (h : Head) (u : Vec) (k : Nat) :
    h.ov 20 u k = sumN 20 (fun b => coords u b * h.ov 20 (Bcol b) k) := by
  rw [Head.ov_eqOn h 20 _ _ (recon u)]
  unfold Head.ov
  rw [show mulVec h.WV 20 (fun r => sumN 20 (fun a => B r a * coords u a)) =
      fun c => sumN 20 (fun a => coords u a * mulVec h.WV 20 (Bcol a) c) by
    funext c; rw [mulVec_comb]; rfl]
  unfold mulVec
  rw [show (fun c => h.WO k c * sumN 20 (fun a => coords u a * sumN 20 (fun r => h.WV c r * Bcol a r))) =
      fun c => sumN 20 (fun a => coords u a * (h.WO k c * sumN 20 (fun r => h.WV c r * Bcol a r))) by
    funext c; rw [← sumN_mul_left]; apply sumN_congr; intro a _; grind]
  rw [sumN_comm]; apply sumN_congr; intro a _; rw [← sumN_mul_left]

/-- **Head 1's QK form on any two residual vectors.** -/
theorem qk1_closed (u v : Vec) :
    qk1 u v = 4 * sumN 7 (fun p => coords u (5 + p) * coords v (4 + p)) := by
  unfold qk1; rw [qk_expand]
  rw [show (fun a => sumN 20 (fun b => coords u a * coords v b * whisper.h1.qk 20 (Bcol a) (Bcol b))) =
      fun a => sumN 20 (fun b => coords u a * coords v b * QK1B a b) from rfl]
  rw [sumN_congr 20 _ _ (fun a ha => sumN_congr 20 _ _ (fun b hb => by rw [QK1B_eq a ha b hb]))]
  simp only [sumN]
  simp
  grind

/-- **Head 2's QK form on any two residual vectors.** -/
theorem qk2_closed (u v : Vec) :
    qk2 u v = sumN 4 (fun t => coords u t *
      (10 * coords v (12 + t) + sumN 8 (fun p => w p * coords v (4 + p)))) := by
  unfold qk2; rw [qk_expand]
  rw [show (fun a => sumN 20 (fun b => coords u a * coords v b * whisper.h2.qk 20 (Bcol a) (Bcol b))) =
      fun a => sumN 20 (fun b => coords u a * coords v b * QK2B a b) from rfl]
  rw [sumN_congr 20 _ _ (fun a ha => sumN_congr 20 _ _ (fun b hb => by rw [QK2B_eq a ha b hb]))]
  simp only [sumN, w]
  simp
  grind

/-- **Head 1's OV map on any residual vector**: it moves the token block into
the "previous token" block and annihilates everything else. -/
theorem ov1_closed (u : Vec) (a : Nat) (ha : a < 20) :
    coords (ov1 u) a = if 12 ≤ a ∧ a < 16 then coords u (a - 12) else 0 := by
  have : coords (ov1 u) a = sumN 20 (fun b => coords u b * OV1B a b) := by
    show sumN 20 (fun r => Binv a r * ov1 u r) = _
    rw [sumN_congr 20 _ (fun r => Binv a r * sumN 20 (fun b => coords u b * ov1 (Bcol b) r))
      (fun r _ => by rw [show ov1 u r = _ from ov_expand whisper.h1 u r]; rfl)]
    rw [show (fun r => Binv a r * sumN 20 (fun b => coords u b * ov1 (Bcol b) r)) =
        fun r => sumN 20 (fun b => coords u b * (Binv a r * ov1 (Bcol b) r)) by
      funext r; rw [← sumN_mul_left]; apply sumN_congr; intro b _; grind]
    rw [sumN_comm]; apply sumN_congr; intro b _; rw [sumN_mul_left]; rfl
  rw [this, sumN_congr 20 _ _ (fun b hb => by rw [OV1B_eq a ha b hb])]
  by_cases h : 12 ≤ a ∧ a < 16
  · rw [ite_eq_left h, sumN_single 20 _ (a - 12) (by omega)
      (fun b _ hb => by rw [ite_eq_right (by omega)]; simp)]
    rw [ite_eq_left (by omega)]; simp
  · rw [ite_eq_right h]; apply sumN_eq_zero; intro b _; rw [ite_eq_right (by omega)]; simp

/-- **Head 2's OV map on any residual vector**: token block → output block. -/
theorem ov2_closed (u : Vec) (a : Nat) (ha : a < 20) :
    coords (ov2 u) a = if 16 ≤ a then coords u (a - 16) else 0 := by
  have : coords (ov2 u) a = sumN 20 (fun b => coords u b * OV2B a b) := by
    show sumN 20 (fun r => Binv a r * ov2 u r) = _
    rw [sumN_congr 20 _ (fun r => Binv a r * sumN 20 (fun b => coords u b * ov2 (Bcol b) r))
      (fun r _ => by rw [show ov2 u r = _ from ov_expand whisper.h2 u r]; rfl)]
    rw [show (fun r => Binv a r * sumN 20 (fun b => coords u b * ov2 (Bcol b) r)) =
        fun r => sumN 20 (fun b => coords u b * (Binv a r * ov2 (Bcol b) r)) by
      funext r; rw [← sumN_mul_left]; apply sumN_congr; intro b _; grind]
    rw [sumN_comm]; apply sumN_congr; intro b _; rw [sumN_mul_left]; rfl
  rw [this, sumN_congr 20 _ _ (fun b hb => by rw [OV2B_eq a ha b hb])]
  by_cases h : 16 ≤ a
  · rw [ite_eq_left h, sumN_single 20 _ (a - 16) (by omega)
      (fun b _ hb => by rw [ite_eq_right (by omega)]; simp)]
    rw [ite_eq_left (by omega)]; simp
  · rw [ite_eq_right h]; apply sumN_eq_zero; intro b _; rw [ite_eq_right (by omega)]; simp

/-- **The unembedding on any residual vector**: logit `t` is `5 ×` the
`O t` coordinate. -/
theorem unembed_closed (t : Nat) (ht : t < 4) (u : Vec) :
    unembed t u = 5 * coords u (16 + t) := by
  unfold unembed
  rw [dot_eqOn 20 _ _ _ _ (EqOn.refl _ _) (recon u)]
  have : dot 20 (row whisper.WU t) (fun r => sumN 20 (fun a => B r a * coords u a)) =
      sumN 20 (fun a => coords u a * UB t a) := by
    unfold dot UB unembed dot
    rw [show (fun k => row whisper.WU t k * sumN 20 (fun a => B k a * coords u a)) =
        fun k => sumN 20 (fun a => coords u a * (row whisper.WU t k * Bcol a k)) by
      funext k; rw [← sumN_mul_left]; apply sumN_congr; intro a _; unfold B; grind]
    rw [sumN_comm]; apply sumN_congr; intro a _; rw [← sumN_mul_left]
  rw [this, sumN_congr 20 _ _ (fun a ha => by rw [UB_eq t ht a ha]),
    sumN_single 20 _ (t + 16) (by omega) (fun a _ ha => by rw [ite_eq_right ha]; simp)]
  rw [ite_eq_left rfl, Nat.add_comm]; grind

end Whisperheard.Interp
