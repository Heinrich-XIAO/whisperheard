import Whisperheard.Model

/-!
# From circuit tables to an exact formula for the whole network

`Spec M c1 cm cU w` records a complete set of circuit tables, in terms of the
four vector families

* `tok t` (token embedding), `pos p` (positional embedding),
* `S t := OV₁ (tok t)` (head-1 output), `O t := OV₂ (tok t)` (head-2 output),

with **symbolic** strengths `c1 cm cU` and positional key ramp `w`. The main
result, `Spec.predict_eq`, says that *any* network satisfying such tables
computes

  `predict x i = x (argmax_{j ≤ i} (cm·[x i = x (prev j)] + w j))`

where `prev j = j - 1` inside the window (and `0` elsewhere). The concrete
network instantiates this in `Whisperheard.Interp.Whisper`; ablated networks
instantiate it with different constants in `Whisperheard.Interp.Ablations`.

Nothing here is specific to the hidden basis, and nothing is approximate.
-/

namespace Whisperheard

/-! ## Linearity of heads -/

namespace Head
variable (h : Head) (d : Nat)

theorem qk_add_left (a b c : Vec) : h.qk d (a ⊞ b) c = h.qk d a c + h.qk d b c := by
  unfold qk q; rw [mulVec_add, dot_add_left]
theorem qk_add_right (a b c : Vec) : h.qk d a (b ⊞ c) = h.qk d a b + h.qk d a c := by
  unfold qk k; rw [mulVec_add, dot_add_right]
theorem qk_zero_left (b : Vec) : h.qk d zeroV b = 0 := by
  unfold qk q; rw [mulVec_zero, dot_zero_left]
theorem qk_zero_right (a : Vec) : h.qk d a zeroV = 0 := by
  unfold qk k; rw [mulVec_zero, dot_zero_right]
theorem qk_eqOn (a a' b b' : Vec) (ha : EqOn d a a') (hb : EqOn d b b') :
    h.qk d a b = h.qk d a' b' := by
  unfold qk q k; rw [mulVec_eqOn _ _ _ _ ha, mulVec_eqOn _ _ _ _ hb]
theorem ov_add (a b : Vec) : h.ov d (a ⊞ b) = h.ov d a ⊞ h.ov d b := by
  unfold ov; rw [mulVec_add, mulVec_add]
theorem ov_zero : h.ov d zeroV = zeroV := by
  unfold ov; rw [mulVec_zero, mulVec_zero]
theorem ov_eqOn (a a' : Vec) (ha : EqOn d a a') : h.ov d a = h.ov d a' := by
  unfold ov; rw [mulVec_eqOn _ _ _ _ ha]

end Head

/-- Where head 1 attends: the previous position inside the window, else `0`. -/
def prevPos (N i : Nat) : Nat := if 1 ≤ i ∧ i < N then i - 1 else 0

/-- The head-2 score formula: match bonus plus positional ramp. -/
def score2Form (N : Nat) (cm : Int) (w : Nat → Int) (x : Nat → Nat) (i j : Nat) : Int :=
  (if x i = x (prevPos N j) then cm else 0) + (if j < N then w j else 0)

namespace Model
variable (M : Model)
/-- What head 1 writes when it attends to a position holding token `t`. -/
def S (t : Nat) : Vec := M.h1.ov M.d (M.tok t)
/-- What head 2 writes when it attends to a position holding token `t`. -/
def O (t : Nat) : Vec := M.h2.ov M.d (M.tok t)
/-- Logit of token `t` read off a residual vector. -/
def unembed (t : Nat) (a : Vec) : Int := dot M.d (row M.WU t) a
end Model

/-- A complete set of circuit tables for a network `M`. -/
structure Spec (M : Model) (c1 cm cU : Int) (w : Nat → Int) : Prop where
  pos_out : ∀ p, M.N ≤ p → M.pos p = zeroV
  -- head 1 QK
  qk1_TT : ∀ t, t < M.V → ∀ t', t' < M.V → M.h1.qk M.d (M.tok t) (M.tok t') = 0
  qk1_TP : ∀ t, t < M.V → ∀ p, p < M.N → M.h1.qk M.d (M.tok t) (M.pos p) = 0
  qk1_PT : ∀ p, p < M.N → ∀ t, t < M.V → M.h1.qk M.d (M.pos p) (M.tok t) = 0
  qk1_PP : ∀ p, p < M.N → ∀ p', p' < M.N →
    M.h1.qk M.d (M.pos p) (M.pos p') = if p = p' + 1 then c1 else 0
  -- head 1 OV
  ov1_P : ∀ p, p < M.N → EqOn M.d (M.h1.ov M.d (M.pos p)) zeroV
  -- head 2 QK
  qk2_TT : ∀ t, t < M.V → ∀ t', t' < M.V → M.h2.qk M.d (M.tok t) (M.tok t') = 0
  qk2_TP : ∀ t, t < M.V → ∀ p, p < M.N → M.h2.qk M.d (M.tok t) (M.pos p) = w p
  qk2_TS : ∀ t, t < M.V → ∀ s, s < M.V →
    M.h2.qk M.d (M.tok t) (M.S s) = if t = s then cm else 0
  qk2_PT : ∀ p, p < M.N → ∀ t, t < M.V → M.h2.qk M.d (M.pos p) (M.tok t) = 0
  qk2_PP : ∀ p, p < M.N → ∀ p', p' < M.N → M.h2.qk M.d (M.pos p) (M.pos p') = 0
  qk2_PS : ∀ p, p < M.N → ∀ s, s < M.V → M.h2.qk M.d (M.pos p) (M.S s) = 0
  qk2_ST : ∀ s, s < M.V → ∀ t, t < M.V → M.h2.qk M.d (M.S s) (M.tok t) = 0
  qk2_SP : ∀ s, s < M.V → ∀ p, p < M.N → M.h2.qk M.d (M.S s) (M.pos p) = 0
  qk2_SS : ∀ s, s < M.V → ∀ s', s' < M.V → M.h2.qk M.d (M.S s) (M.S s') = 0
  -- head 2 OV
  ov2_P : ∀ p, p < M.N → EqOn M.d (M.h2.ov M.d (M.pos p)) zeroV
  ov2_S : ∀ s, s < M.V → EqOn M.d (M.h2.ov M.d (M.S s)) zeroV
  -- unembedding
  U_T : ∀ t, t < M.V → ∀ t', t' < M.V → M.unembed t (M.tok t') = 0
  U_P : ∀ t, t < M.V → ∀ p, p < M.N → M.unembed t (M.pos p) = 0
  U_S : ∀ t, t < M.V → ∀ s, s < M.V → M.unembed t (M.S s) = 0
  U_O : ∀ t, t < M.V → ∀ s, s < M.V → M.unembed t (M.O s) = if t = s then cU else 0

namespace Spec
variable {M : Model} {c1 cm cU : Int} {w : Nat → Int} (hs : Spec M c1 cm cU w)
variable {x : Nat → Nat}
include hs

/-! ### Totalised tables (positions outside the window included) -/

theorem qk1_TP' (t : Nat) (ht : t < M.V) (p : Nat) : M.h1.qk M.d (M.tok t) (M.pos p) = 0 := by
  by_cases hp : p < M.N
  · exact hs.qk1_TP t ht p hp
  · rw [hs.pos_out p (by omega)]; exact Head.qk_zero_right _ _ _

theorem qk1_PT' (p : Nat) (t : Nat) (ht : t < M.V) : M.h1.qk M.d (M.pos p) (M.tok t) = 0 := by
  by_cases hp : p < M.N
  · exact hs.qk1_PT p hp t ht
  · rw [hs.pos_out p (by omega)]; exact Head.qk_zero_left _ _ _

theorem qk1_PP' (p p' : Nat) :
    M.h1.qk M.d (M.pos p) (M.pos p') = if p < M.N ∧ p = p' + 1 then c1 else 0 := by
  by_cases hp : p < M.N
  · by_cases hp' : p' < M.N
    · rw [hs.qk1_PP p hp p' hp']; simp [hp]
    · rw [hs.pos_out p' (by omega), Head.qk_zero_right]
      rw [ite_eq_right (by omega)]
  · rw [hs.pos_out p (by omega), Head.qk_zero_left, ite_eq_right (by omega)]

theorem ov1_P' (p : Nat) : EqOn M.d (M.h1.ov M.d (M.pos p)) zeroV := by
  by_cases hp : p < M.N
  · exact hs.ov1_P p hp
  · rw [hs.pos_out p (by omega), Head.ov_zero]; exact EqOn.refl _ _

theorem qk2_TP' (t : Nat) (ht : t < M.V) (p : Nat) :
    M.h2.qk M.d (M.tok t) (M.pos p) = if p < M.N then w p else 0 := by
  by_cases hp : p < M.N
  · rw [hs.qk2_TP t ht p hp, ite_eq_left hp]
  · rw [hs.pos_out p (by omega), Head.qk_zero_right, ite_eq_right hp]

theorem qk2_PT' (p : Nat) (t : Nat) (ht : t < M.V) : M.h2.qk M.d (M.pos p) (M.tok t) = 0 := by
  by_cases hp : p < M.N
  · exact hs.qk2_PT p hp t ht
  · rw [hs.pos_out p (by omega)]; exact Head.qk_zero_left _ _ _

theorem qk2_PP' (p p' : Nat) : M.h2.qk M.d (M.pos p) (M.pos p') = 0 := by
  by_cases hp : p < M.N
  · by_cases hp' : p' < M.N
    · exact hs.qk2_PP p hp p' hp'
    · rw [hs.pos_out p' (by omega)]; exact Head.qk_zero_right _ _ _
  · rw [hs.pos_out p (by omega)]; exact Head.qk_zero_left _ _ _

theorem qk2_PS' (p : Nat) (s : Nat) (hs' : s < M.V) : M.h2.qk M.d (M.pos p) (M.S s) = 0 := by
  by_cases hp : p < M.N
  · exact hs.qk2_PS p hp s hs'
  · rw [hs.pos_out p (by omega)]; exact Head.qk_zero_left _ _ _

theorem qk2_SP' (s : Nat) (hs' : s < M.V) (p : Nat) : M.h2.qk M.d (M.S s) (M.pos p) = 0 := by
  by_cases hp : p < M.N
  · exact hs.qk2_SP s hs' p hp
  · rw [hs.pos_out p (by omega)]; exact Head.qk_zero_right _ _ _

theorem ov2_P' (p : Nat) : EqOn M.d (M.h2.ov M.d (M.pos p)) zeroV := by
  by_cases hp : p < M.N
  · exact hs.ov2_P p hp
  · rw [hs.pos_out p (by omega), Head.ov_zero]; exact EqOn.refl _ _

theorem U_P' (t : Nat) (ht : t < M.V) (p : Nat) : M.unembed t (M.pos p) = 0 := by
  by_cases hp : p < M.N
  · exact hs.U_P t ht p hp
  · rw [hs.pos_out p (by omega)]; unfold Model.unembed; exact dot_zero_right _ _

/-! ### Layer 1 -/

variable (hx : ∀ k, x k < M.V)
include hx

/-- Head-1 attention scores are a pure function of the two positions. -/
theorem score1_eq (i j : Nat) :
    M.h1.score M.d (M.resid0 x) i j = if i < M.N ∧ i = j + 1 then c1 else 0 := by
  show M.h1.qk M.d (M.tok (x i) ⊞ M.pos i) (M.tok (x j) ⊞ M.pos j) = _
  rw [Head.qk_add_left, Head.qk_add_right, Head.qk_add_right,
    hs.qk1_TT _ (hx i) _ (hx j), hs.qk1_TP' _ (hx i), hs.qk1_PT' _ _ (hx j), hs.qk1_PP']
  simp

/-- **Head 1 is a previous-token head** (inside the window; outside it, it
falls back to position `0`). -/
theorem attn1_eq (hc1 : 0 < c1) (i : Nat) : M.attn1 x i = prevPos M.N i := by
  unfold Model.attn1 Head.attn
  rw [argmaxUpTo_congr _ (fun j => if i < M.N ∧ i = j + 1 then c1 else 0) i
    (fun j _ => hs.score1_eq hx i j)]
  unfold prevPos
  by_cases h : 1 ≤ i ∧ i < M.N
  · rw [ite_eq_left h]
    apply argmaxUpTo_eq_of_strict _ _ _ (by omega)
    intro k _ hk
    have e1 : ¬(i < M.N ∧ i = k + 1) := by omega
    have e2 : i < M.N ∧ i = i - 1 + 1 := by omega
    show (if i < M.N ∧ i = k + 1 then c1 else 0) < (if i < M.N ∧ i = i - 1 + 1 then c1 else 0)
    rw [ite_eq_right e1, ite_eq_left e2]; exact hc1
  · rw [ite_eq_right h]
    apply argmaxUpTo_const _ _ 0
    intro k _
    have e1 : ¬(i < M.N ∧ i = k + 1) := by omega
    show (if i < M.N ∧ i = k + 1 then c1 else 0) = 0
    rw [ite_eq_right e1]

/-- **The residual stream after layer 1**: token, position, and the token
head 1 fetched. -/
theorem resid1_eqOn (hc1 : 0 < c1) (i : Nat) :
    EqOn M.d (M.resid1 x i) (M.tok (x i) ⊞ M.pos i ⊞ M.S (x (prevPos M.N i))) := by
  unfold Model.resid1 Head.out
  have ha : M.h1.attn M.d (M.resid0 x) i = prevPos M.N i := hs.attn1_eq hx hc1 i
  rw [ha]
  show EqOn M.d (M.resid0 x i ⊞ M.h1.ov M.d (M.tok (x (prevPos M.N i)) ⊞ M.pos (prevPos M.N i))) _
  rw [Head.ov_add]
  have := (EqOn.refl M.d (M.S (x (prevPos M.N i)))).add (hs.ov1_P' (prevPos M.N i))
  rw [vadd_zero] at this
  exact (EqOn.refl M.d (M.resid0 x i)).add this

/-! ### Layer 2 -/

theorem score2_eq (hc1 : 0 < c1) (i j : Nat) :
    M.h2.score M.d (M.resid1 x) i j = score2Form M.N cm w x i j := by
  unfold Head.score
  rw [Head.qk_eqOn _ _ _ _ _ _ (hs.resid1_eqOn hx hc1 i) (hs.resid1_eqOn hx hc1 j)]
  simp only [Head.qk_add_left, Head.qk_add_right]
  rw [hs.qk2_TT _ (hx i) _ (hx j), hs.qk2_TP' _ (hx i), hs.qk2_TS _ (hx i) _ (hx _),
    hs.qk2_PT' _ _ (hx j), hs.qk2_PP', hs.qk2_PS' _ _ (hx _),
    hs.qk2_ST _ (hx _) _ (hx j), hs.qk2_SP' _ (hx _), hs.qk2_SS _ (hx _) _ (hx _)]
  unfold score2Form
  omega

/-- **Head 2 is an induction head**: it attends to the argmax of the explicit
score `cm·[x i = x (prev j)] + w j`. -/
theorem attn2_eq (hc1 : 0 < c1) (i : Nat) :
    M.attn2 x i = argmaxUpTo (score2Form M.N cm w x i) i := by
  unfold Model.attn2 Head.attn
  exact argmaxUpTo_congr _ _ i (fun j _ => hs.score2_eq hx hc1 i j)

/-- **Exact logits**: the network outputs `cU` on the token at the attended
position and exactly `0` on every other token. All other paths cancel. -/
theorem logits_eq (hc1 : 0 < c1) (i t : Nat) (ht : t < M.V) :
    M.logits x i t = if t = x (M.attn2 x i) then cU else 0 := by
  unfold Model.logits Model.resid2 Head.out Model.attn2
  generalize ha : M.h2.attn M.d (M.resid1 x) i = a
  have h1 := hs.resid1_eqOn hx hc1 i
  have h2 := hs.resid1_eqOn hx hc1 a
  rw [Head.ov_eqOn _ _ _ _ h2, Head.ov_add, Head.ov_add]
  have hz : EqOn M.d (M.h2.ov M.d (M.tok (x a)) ⊞ M.h2.ov M.d (M.pos a) ⊞
      M.h2.ov M.d (M.S (x (prevPos M.N a)))) (M.O (x a)) := by
    have := ((EqOn.refl M.d (M.O (x a))).add (hs.ov2_P' a)).add (hs.ov2_S _ (hx (prevPos M.N a)))
    rw [vadd_zero, vadd_zero] at this; exact this
  rw [dot_eqOn _ _ _ _ _ (EqOn.refl _ _) (h1.add hz)]
  simp only [dot_add_right]
  have e1 := hs.U_T t ht _ (hx i)
  have e2 := hs.U_P' t ht i
  have e3 := hs.U_S t ht _ (hx (prevPos M.N i))
  have e4 := hs.U_O t ht _ (hx a)
  unfold Model.unembed at e1 e2 e3 e4
  rw [e1, e2, e3, e4]; simp

/-- **The residual stream after layer 2**: token, position, head 1's fetch,
and head 2's fetch, nothing else. -/
theorem resid2_eqOn (hc1 : 0 < c1) (i : Nat) :
    EqOn M.d (M.resid2 x i) (M.tok (x i) ⊞ M.pos i ⊞ M.S (x (prevPos M.N i)) ⊞ M.O (x (M.attn2 x i))) := by
  unfold Model.resid2 Head.out Model.attn2
  generalize M.h2.attn M.d (M.resid1 x) i = a
  rw [Head.ov_eqOn _ _ _ _ (hs.resid1_eqOn hx hc1 a), Head.ov_add, Head.ov_add]
  have hz := ((EqOn.refl M.d (M.O (x a))).add (hs.ov2_P' a)).add (hs.ov2_S _ (hx (prevPos M.N a)))
  rw [vadd_zero, vadd_zero] at hz
  exact (hs.resid1_eqOn hx hc1 i).add hz

/-- **The network copies the token head 2 attends to.** -/
theorem predict_eq (hc1 : 0 < c1) (hcU : 0 < cU) (i : Nat) :
    M.predict x i = x (M.attn2 x i) := by
  unfold Model.predict
  have hV : 0 < M.V := by have := hx 0; omega
  apply argmaxUpTo_eq_of_strict _ _ _ (by have := hx (M.attn2 x i); omega)
  intro t ht hne
  rw [hs.logits_eq hx hc1 i t (by omega), hs.logits_eq hx hc1 i _ (hx _), ite_eq_right hne, ite_eq_left rfl]
  exact hcU

/-- Combined: the full network as one formula. -/
theorem predict_formula (hc1 : 0 < c1) (hcU : 0 < cU) (i : Nat) :
    M.predict x i = x (argmaxUpTo (score2Form M.N cm w x i) i) := by
  rw [hs.predict_eq hx hc1 hcU, hs.attn2_eq hx hc1]

/-- If the unembedding gain is zero the network is constant. -/
theorem predict_of_cU_zero (hc1 : 0 < c1) (hcU : cU = 0) (i : Nat) : M.predict x i = 0 := by
  unfold Model.predict
  apply argmaxUpTo_const _ _ 0
  intro t ht
  have hV : 0 < M.V := by have := hx 0; omega
  rw [hs.logits_eq hx hc1 i t (by omega)]; split <;> omega

end Spec
end Whisperheard
