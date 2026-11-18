import Whisperheard.Interp.Mechanism

/-!
# Symmetries: what can and cannot be recovered from weights

1. **Heads matter only through their QK form and OV map** (`predict_congr`):
   two networks whose heads have the same `qk` and `ov` compute the same
   function.
2. **Head-internal bases are pure gauge** (`qk_gauge`, `ov_gauge`):
   `WQ ↦ R·WQ, WK ↦ R'·WK` with `Rᵀ R' = I`, and `WV ↦ A·WV, WO ↦ WO·A'`
   with `A' A = I`, change nothing. So the raw `WQ, WK, WV, WO` are not
   meaningful individually; only `WQᵀWK` and `WO WV` are.
3. **The residual basis is pure gauge** (`conj_predict`): conjugating every
   weight by a unimodular `U` (reading weights `· U⁻¹`, writing weights
   `U ·`) changes nothing. This is exactly how `scripts/Gen.lean` hid the
   clean weights, so this theorem certifies that the hiding was harmless.

Together: the circuit tables / closed forms in `Basis` are a *complete*
invariant description of the network; there is nothing further to read off
the weights.
-/

namespace Whisperheard

/-! ## 1. Heads matter only through `qk` and `ov` -/

theorem Head.attn_congr (h h' : Head) (d : Nat) (e : ∀ a b, h'.qk d a b = h.qk d a b)
    (r : Nat → Vec) (i : Nat) : h'.attn d r i = h.attn d r i := by
  unfold Head.attn; apply argmaxUpTo_congr; intro k _; unfold Head.score; rw [e]

theorem Head.out_congr (h h' : Head) (d : Nat) (e : ∀ a b, h'.qk d a b = h.qk d a b)
    (e' : ∀ a, h'.ov d a = h.ov d a) (r : Nat → Vec) (i : Nat) :
    h'.out d r i = h.out d r i := by
  unfold Head.out; rw [Head.attn_congr h h' d e, e']

theorem predict_congr (M : Model) (g1 g2 : Head)
    (e1 : ∀ a b, g1.qk M.d a b = M.h1.qk M.d a b) (e1' : ∀ a, g1.ov M.d a = M.h1.ov M.d a)
    (e2 : ∀ a b, g2.qk M.d a b = M.h2.qk M.d a b) (e2' : ∀ a, g2.ov M.d a = M.h2.ov M.d a)
    (x : Nat → Nat) (i : Nat) :
    ({ M with h1 := g1, h2 := g2 } : Model).predict x i = M.predict x i := by
  have r1 : ({ M with h1 := g1, h2 := g2 } : Model).resid1 x = M.resid1 x := by
    funext j; unfold Model.resid1
    show M.resid0 x j ⊞ g1.out M.d (M.resid0 x) j = _
    rw [Head.out_congr _ _ _ e1 e1']
  have r2 : ({ M with h1 := g1, h2 := g2 } : Model).resid2 x = M.resid2 x := by
    funext j; unfold Model.resid2; rw [r1]
    show M.resid1 x j ⊞ g2.out M.d (M.resid1 x) j = _
    rw [Head.out_congr _ _ _ e2 e2']
  unfold Model.predict Model.logits; rw [r2]

/-! ## 2. Head-internal gauge -/

theorem qk_gauge (h : Head) (d : Nat) (R R' : Mat)
    (hR : ∀ a, a < h.dh → ∀ b, b < h.dh → mmul (transpose R) R' h.dh a b = if a = b then 1 else 0)
    (u v : Vec) :
    ({ h with WQ := mmul R h.WQ h.dh, WK := mmul R' h.WK h.dh } : Head).qk d u v = h.qk d u v := by
  unfold Head.qk Head.q Head.k
  simp only
  rw [mulVec_mmul, mulVec_mmul, dot_mulVec_left, ← mulVec_mmul]
  exact dot_eqOn _ _ _ _ _ (EqOn.refl _ _) (mulVec_id _ _ hR _)

theorem ov_gauge (h : Head) (d : Nat) (A A' : Mat)
    (hA : ∀ a, a < h.dv → ∀ b, b < h.dv → mmul A' A h.dv a b = if a = b then 1 else 0) (u : Vec) :
    ({ h with WV := mmul A h.WV h.dv, WO := mmul h.WO A' h.dv } : Head).ov d u = h.ov d u := by
  unfold Head.ov
  simp only
  rw [mulVec_mmul, mulVec_mmul, ← mulVec_mmul A' A]
  exact mulVec_eqOn _ _ _ _ (mulVec_id _ _ hA _)

/-! ## 3. Residual-stream gauge -/

/-- Conjugate a head by a change of residual basis (`U` writes, `Ui` reads). -/
def Head.conj (h : Head) (d : Nat) (U Ui : Mat) : Head :=
  { h with WQ := mmul h.WQ Ui d, WK := mmul h.WK Ui d, WV := mmul h.WV Ui d,
           WO := mmul U h.WO d }

/-- Conjugate a whole network by a change of residual basis. -/
def Model.conj (M : Model) (U Ui : Mat) : Model :=
  { M with WE := mmul U M.WE M.d, WP := mmul U M.WP M.d, WU := mmul M.WU Ui M.d,
           h1 := M.h1.conj M.d U Ui, h2 := M.h2.conj M.d U Ui }

section
variable (d : Nat) (U Ui : Mat)
  (hU : ∀ a, a < d → ∀ b, b < d → mmul Ui U d a b = if a = b then 1 else 0)
include hU

theorem read_conj (A : Mat) (v : Vec) : mulVec (mmul A Ui d) d (mulVec U d v) = mulVec A d v := by
  rw [mulVec_mmul, ← mulVec_mmul Ui U]; exact mulVec_eqOn _ _ _ _ (mulVec_id _ _ hU _)

theorem qk_conj (h : Head) (a b : Vec) :
    (h.conj d U Ui).qk d (mulVec U d a) (mulVec U d b) = h.qk d a b := by
  unfold Head.qk Head.q Head.k Head.conj; simp only; rw [read_conj d U Ui hU, read_conj d U Ui hU]

omit hU in
theorem ov_conj' (h : Head) (a : Vec) (hU : ∀ a, a < d → ∀ b, b < d → mmul Ui U d a b = if a = b then 1 else 0) :
    (h.conj d U Ui).ov d (mulVec U d a) = mulVec U d (h.ov d a) := by
  unfold Head.ov Head.conj; simp only; rw [read_conj d U Ui hU, mulVec_mmul]

end

/-- **Conjugating the residual stream by an invertible integer matrix changes
nothing**: same attention everywhere, same logits, same predictions. -/
theorem conj_predict (M : Model) (U Ui : Mat)
    (hU : ∀ a, a < M.d → ∀ b, b < M.d → mmul Ui U M.d a b = if a = b then 1 else 0)
    (x : Nat → Nat) (i : Nat) : (M.conj U Ui).predict x i = M.predict x i := by
  have e0 : ∀ j, (M.conj U Ui).resid0 x j = mulVec U M.d (M.resid0 x j) := by
    intro j; unfold Model.resid0 Model.tok Model.pos Model.conj col
    funext r; simp only; unfold vadd mmul mulVec
    rw [← sumN_add]; apply sumN_congr; intro k _; grind
  have a1 : ∀ j, (M.conj U Ui).attn1 x j = M.attn1 x j := by
    intro j; unfold Model.attn1 Head.attn
    apply argmaxUpTo_congr; intro k _; unfold Head.score
    rw [e0, e0]; exact qk_conj M.d U Ui hU M.h1 _ _
  have e1 : ∀ j, (M.conj U Ui).resid1 x j = mulVec U M.d (M.resid1 x j) := by
    intro j; unfold Model.resid1 Head.out
    rw [show (M.conj U Ui).h1.attn (M.conj U Ui).d ((M.conj U Ui).resid0 x) j = M.attn1 x j from a1 j]
    rw [e0, e0, mulVec_add]
    show _ ⊞ (M.h1.conj M.d U Ui).ov M.d _ = _
    rw [ov_conj' M.d U Ui M.h1 _ hU]; rfl
  have a2 : ∀ j, (M.conj U Ui).attn2 x j = M.attn2 x j := by
    intro j; unfold Model.attn2 Head.attn
    apply argmaxUpTo_congr; intro k _; unfold Head.score
    rw [e1, e1]; exact qk_conj M.d U Ui hU M.h2 _ _
  have e2 : ∀ j, (M.conj U Ui).resid2 x j = mulVec U M.d (M.resid2 x j) := by
    intro j; unfold Model.resid2 Head.out
    rw [show (M.conj U Ui).h2.attn (M.conj U Ui).d ((M.conj U Ui).resid1 x) j = M.attn2 x j from a2 j]
    rw [e1, e1, mulVec_add]
    show _ ⊞ (M.h2.conj M.d U Ui).ov M.d _ = _
    rw [ov_conj' M.d U Ui M.h2 _ hU]; rfl
  unfold Model.predict
  apply argmaxUpTo_congr; intro t _
  unfold Model.logits; rw [e2]
  show dot M.d (row (mmul M.WU Ui M.d) t) (mulVec U M.d (M.resid2 x i)) = _
  rw [show row (mmul M.WU Ui M.d) t = fun c => mulVec (transpose Ui) M.d (row M.WU t) c by
    funext c; unfold row mmul mulVec transpose; apply sumN_congr; intro k _; exact Int.mul_comm _ _]
  rw [show (fun c => mulVec (transpose Ui) M.d (row M.WU t) c) = mulVec (transpose Ui) M.d (row M.WU t) from rfl]
  rw [show dot M.d (mulVec (transpose Ui) M.d (row M.WU t)) (mulVec U M.d (M.resid2 x i)) =
      dot M.d (row M.WU t) (mulVec (transpose (transpose Ui)) M.d (mulVec U M.d (M.resid2 x i)))
      from dot_mulVec_left _ _ _ _ _]
  rw [show transpose (transpose Ui) = Ui from rfl, ← mulVec_mmul]
  exact dot_eqOn _ _ _ _ _ (EqOn.refl _ _) (mulVec_id _ _ hU _)

end Whisperheard
