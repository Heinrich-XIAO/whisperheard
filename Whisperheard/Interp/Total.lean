import Whisperheard.Interp.Whisper

/-!
# The law on *every* input stream, including out-of-vocabulary tokens

The model's input type is `Nat → Nat`, so tokens `≥ 4` are possible inputs.
Their embedding column does not exist, so they embed to the zero vector.
Tracing that through the mechanism gives a law with no hypotheses at all:

  `whisper.predict x i =`
    let `a := if x i < 4 then target 8 x i else 0`
    `if x a < 4 then x a else 0`

In words: an out-of-vocabulary *query* switches head 2's query off entirely
(all scores `0`, so it attends to position `0`); an out-of-vocabulary token
at the *attended* position writes nothing, so all logits are `0` and the
first token, `0`, wins.
-/

namespace Whisperheard

namespace Spec
variable {M : Model} {c1 cm cU : Int} {w : Nat → Int} (hs : Spec M c1 cm cU w)
  (hT : ∀ t, M.V ≤ t → M.tok t = zeroV)
include hs hT

omit hs in
theorem S_out (t : Nat) (ht : M.V ≤ t) : M.S t = zeroV := by
  unfold Model.S; rw [hT t ht, Head.ov_zero]

omit hs in
theorem O_out (t : Nat) (ht : M.V ≤ t) : M.O t = zeroV := by
  unfold Model.O; rw [hT t ht, Head.ov_zero]

omit hs in
/-- Rewrite a token embedding to zero when the token is out of range. -/
theorem tokz {t : Nat} (ht : ¬ t < M.V) : M.tok t = zeroV := hT t (by omega)

theorem qk1_TT_all (t t' : Nat) : M.h1.qk M.d (M.tok t) (M.tok t') = 0 := by
  by_cases h : t < M.V
  · by_cases h' : t' < M.V
    · exact hs.qk1_TT t h t' h'
    · rw [tokz hT h']; exact Head.qk_zero_right _ _ _
  · rw [tokz hT h]; exact Head.qk_zero_left _ _ _

theorem qk1_TP_all (t p : Nat) : M.h1.qk M.d (M.tok t) (M.pos p) = 0 := by
  by_cases h : t < M.V
  · exact hs.qk1_TP' t h p
  · rw [tokz hT h]; exact Head.qk_zero_left _ _ _

theorem qk1_PT_all (p t : Nat) : M.h1.qk M.d (M.pos p) (M.tok t) = 0 := by
  by_cases h : t < M.V
  · exact hs.qk1_PT' p t h
  · rw [tokz hT h]; exact Head.qk_zero_right _ _ _

theorem score1_total (x : Nat → Nat) (i j : Nat) :
    M.h1.score M.d (M.resid0 x) i j = if i < M.N ∧ i = j + 1 then c1 else 0 := by
  show M.h1.qk M.d (M.tok (x i) ⊞ M.pos i) (M.tok (x j) ⊞ M.pos j) = _
  rw [Head.qk_add_left, Head.qk_add_right, Head.qk_add_right,
    hs.qk1_TT_all hT, hs.qk1_TP_all hT, hs.qk1_PT_all hT, hs.qk1_PP']
  simp

theorem attn1_total (hc1 : 0 < c1) (x : Nat → Nat) (i : Nat) : M.attn1 x i = prevPos M.N i := by
  unfold Model.attn1 Head.attn
  rw [argmaxUpTo_congr _ (fun j => if i < M.N ∧ i = j + 1 then c1 else 0) i
    (fun j _ => hs.score1_total hT x i j)]
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

theorem resid1_total (hc1 : 0 < c1) (x : Nat → Nat) (i : Nat) :
    EqOn M.d (M.resid1 x i) (M.tok (x i) ⊞ M.pos i ⊞ M.S (x (prevPos M.N i))) := by
  unfold Model.resid1 Head.out
  have ha : M.h1.attn M.d (M.resid0 x) i = prevPos M.N i := hs.attn1_total hT hc1 x i
  rw [ha]
  show EqOn M.d (M.resid0 x i ⊞ M.h1.ov M.d (M.tok (x (prevPos M.N i)) ⊞ M.pos (prevPos M.N i))) _
  rw [Head.ov_add]
  have := (EqOn.refl M.d (M.S (x (prevPos M.N i)))).add (hs.ov1_P' (prevPos M.N i))
  rw [vadd_zero] at this
  exact (EqOn.refl M.d (M.resid0 x i)).add this

/-- Head-2 scores on an arbitrary stream: the usual formula for an in-range
query, identically `0` for an out-of-range one. -/
theorem score2_total (hc1 : 0 < c1) (x : Nat → Nat) (i j : Nat) :
    M.h2.score M.d (M.resid1 x) i j = if x i < M.V then score2Form M.N cm w x i j else 0 := by
  unfold Head.score
  rw [Head.qk_eqOn _ _ _ _ _ _ (hs.resid1_total hT hc1 x i) (hs.resid1_total hT hc1 x j)]
  simp only [Head.qk_add_left, Head.qk_add_right]
  -- the query's position and head-1 parts never contribute
  have zP : ∀ v, v = M.tok (x j) ∨ v = M.pos j ∨ v = M.S (x (prevPos M.N j)) →
      M.h2.qk M.d (M.pos i) v = 0 := by
    intro v hv; rcases hv with rfl | rfl | rfl
    · by_cases h : x j < M.V
      · exact hs.qk2_PT' i _ h
      · rw [tokz hT h]; exact Head.qk_zero_right _ _ _
    · exact hs.qk2_PP' i j
    · by_cases h : x (prevPos M.N j) < M.V
      · exact hs.qk2_PS' i _ h
      · rw [S_out hT (x (prevPos M.N j)) (by omega)]; exact Head.qk_zero_right _ _ _
  have zS : ∀ v, v = M.tok (x j) ∨ v = M.pos j ∨ v = M.S (x (prevPos M.N j)) →
      M.h2.qk M.d (M.S (x (prevPos M.N i))) v = 0 := by
    intro v hv
    by_cases hq : x (prevPos M.N i) < M.V
    · rcases hv with rfl | rfl | rfl
      · by_cases h : x j < M.V
        · exact hs.qk2_ST _ hq _ h
        · rw [tokz hT h]; exact Head.qk_zero_right _ _ _
      · exact hs.qk2_SP' _ hq j
      · by_cases h : x (prevPos M.N j) < M.V
        · exact hs.qk2_SS _ hq _ h
        · rw [S_out hT (x (prevPos M.N j)) (by omega)]; exact Head.qk_zero_right _ _ _
    · rw [S_out hT (x (prevPos M.N i)) (by omega)]; exact Head.qk_zero_left _ _ _
  rw [zP _ (Or.inl rfl), zP _ (Or.inr (Or.inl rfl)), zP _ (Or.inr (Or.inr rfl)),
    zS _ (Or.inl rfl), zS _ (Or.inr (Or.inl rfl)), zS _ (Or.inr (Or.inr rfl))]
  by_cases hq : x i < M.V
  · rw [ite_eq_left hq]
    have tt : M.h2.qk M.d (M.tok (x i)) (M.tok (x j)) = 0 := by
      by_cases h : x j < M.V
      · exact hs.qk2_TT _ hq _ h
      · rw [tokz hT h]; exact Head.qk_zero_right _ _ _
    have ts : M.h2.qk M.d (M.tok (x i)) (M.S (x (prevPos M.N j))) =
        if x i = x (prevPos M.N j) then cm else 0 := by
      by_cases h : x (prevPos M.N j) < M.V
      · exact hs.qk2_TS _ hq _ h
      · rw [S_out hT (x (prevPos M.N j)) (by omega), Head.qk_zero_right, ite_eq_right (by omega)]
    rw [tt, hs.qk2_TP' _ hq, ts]; unfold score2Form; omega
  · rw [ite_eq_right hq, tokz hT hq, Head.qk_zero_left, Head.qk_zero_left, Head.qk_zero_left]
    simp

theorem attn2_total (hc1 : 0 < c1) (x : Nat → Nat) (i : Nat) :
    M.attn2 x i = if x i < M.V then argmaxUpTo (score2Form M.N cm w x i) i else 0 := by
  unfold Model.attn2 Head.attn
  by_cases hq : x i < M.V
  · rw [ite_eq_left hq]
    exact argmaxUpTo_congr _ _ i (fun j _ => by rw [hs.score2_total hT hc1 x i j, ite_eq_left hq])
  · rw [ite_eq_right hq]
    exact argmaxUpTo_const _ _ 0 (fun j _ => by rw [hs.score2_total hT hc1 x i j, ite_eq_right hq])

theorem logits_total (hc1 : 0 < c1) (x : Nat → Nat) (i t : Nat) (ht : t < M.V) :
    M.logits x i t = if x (M.attn2 x i) < M.V ∧ t = x (M.attn2 x i) then cU else 0 := by
  unfold Model.logits Model.resid2 Head.out Model.attn2
  generalize ha : M.h2.attn M.d (M.resid1 x) i = a
  have h1 := hs.resid1_total hT hc1 x i
  have h2 := hs.resid1_total hT hc1 x a
  rw [Head.ov_eqOn _ _ _ _ h2, Head.ov_add, Head.ov_add]
  have zS : EqOn M.d (M.h2.ov M.d (M.S (x (prevPos M.N a)))) zeroV := by
    by_cases h : x (prevPos M.N a) < M.V
    · exact hs.ov2_S _ h
    · rw [S_out hT (x (prevPos M.N a)) (by omega), Head.ov_zero]; exact EqOn.refl _ _
  have hz : EqOn M.d (M.h2.ov M.d (M.tok (x a)) ⊞ M.h2.ov M.d (M.pos a) ⊞
      M.h2.ov M.d (M.S (x (prevPos M.N a)))) (M.O (x a)) := by
    have := ((EqOn.refl M.d (M.O (x a))).add (hs.ov2_P' a)).add zS
    rw [vadd_zero, vadd_zero] at this; exact this
  rw [dot_eqOn _ _ _ _ _ (EqOn.refl _ _) (h1.add hz)]
  simp only [dot_add_right]
  have e1 : dot M.d (row M.WU t) (M.tok (x i)) = 0 := by
    by_cases h : x i < M.V
    · exact hs.U_T t ht _ h
    · rw [tokz hT h]; exact dot_zero_right _ _
  have e2 := hs.U_P' t ht i
  have e3 : dot M.d (row M.WU t) (M.S (x (prevPos M.N i))) = 0 := by
    by_cases h : x (prevPos M.N i) < M.V
    · exact hs.U_S t ht _ h
    · rw [S_out hT (x (prevPos M.N i)) (by omega)]; exact dot_zero_right _ _
  have e4 : dot M.d (row M.WU t) (M.O (x a)) = if x a < M.V ∧ t = x a then cU else 0 := by
    by_cases h : x a < M.V
    · have := hs.U_O t ht _ h; unfold Model.unembed at this; rw [this]; simp [h]
    · rw [O_out hT (x a) (by omega), dot_zero_right, ite_eq_right (by omega)]
  unfold Model.unembed at e2
  rw [e1, e2, e3, e4]; simp

theorem predict_total (hc1 : 0 < c1) (hcU : 0 < cU) (hV : 0 < M.V) (x : Nat → Nat) (i : Nat) :
    M.predict x i = if x (M.attn2 x i) < M.V then x (M.attn2 x i) else 0 := by
  unfold Model.predict
  by_cases h : x (M.attn2 x i) < M.V
  · rw [ite_eq_left h]
    apply argmaxUpTo_eq_of_strict _ _ _ (by omega)
    intro t ht hne
    rw [hs.logits_total hT hc1 x i t (by omega), hs.logits_total hT hc1 x i _ h,
      ite_eq_right (fun h' => hne h'.2), ite_eq_left ⟨h, rfl⟩]
    exact hcU
  · rw [ite_eq_right h]
    apply argmaxUpTo_const _ _ 0
    intro t ht
    rw [hs.logits_total hT hc1 x i t (by omega), ite_eq_right (fun h' => h h'.1)]

end Spec

theorem WE_rows : ∀ r ∈ Weights.WE, r.length = 4 := by decide

theorem tok_out (t : Nat) (ht : whisper.V ≤ t) : whisper.tok t = zeroV := by
  funext k
  show ofRows Weights.WE k t = 0
  apply ofRows_out_col
  intro r hr; rw [WE_rows r hr]; exact ht

/-- **The total law.** No hypotheses: every stream of natural numbers, every
position. -/
theorem predict_whisper_total (x : Nat → Nat) (i : Nat) :
    whisper.predict x i =
      let a := if x i < 4 then target 8 x i else 0
      if x a < 4 then x a else 0 := by
  have ha : whisper.attn2 x i = if x i < 4 then target 8 x i else 0 := by
    rw [whisper_spec.attn2_total tok_out (by decide) x i]
    rw [show whisper.V = 4 from rfl, show whisper.N = 8 from rfl]
    by_cases h : x i < 4
    · rw [ite_eq_left h, ite_eq_left h, argmax_score2_eq_target whisper_lawHyp]
    · rw [ite_eq_right h, ite_eq_right h]
  rw [whisper_spec.predict_total tok_out (by decide) (by decide) (by decide) x i, ha]
  rfl

/-- Head 2's attention on every stream. -/
theorem attn2_whisper_total (x : Nat → Nat) (i : Nat) :
    whisper.attn2 x i = if x i < 4 then target 8 x i else 0 := by
  rw [whisper_spec.attn2_total tok_out (by decide) x i]
  rw [show whisper.V = 4 from rfl, show whisper.N = 8 from rfl]
  by_cases h : x i < 4
  · rw [ite_eq_left h, ite_eq_left h, argmax_score2_eq_target whisper_lawHyp]
  · rw [ite_eq_right h, ite_eq_right h]

/-- Head 1's attention does not even look at tokens. -/
theorem attn1_whisper_total (x : Nat → Nat) (i : Nat) : whisper.attn1 x i = prevPos 8 i :=
  whisper_spec.attn1_total tok_out (by decide) x i

end Whisperheard
