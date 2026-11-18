import Whisperheard.Interp.Mechanism

/-!
# The behavioural law

Pure combinatorics: under a few inequalities on the head-2 constants, the
argmax of `score2Form` is given by a simple search, `target`.

`findMatch x q r` searches `j = r, r-1, …, 1` for the first (i.e. latest) `j`
with `x (j-1) = q` — the position *right after* the latest earlier
occurrence of `q` among `x 0, …, x (r-1)`.

`target N x i`: with `r = min i (N-1)`, the answer of `findMatch x (x i) r`,
defaulting to `r`.
-/

namespace Whisperheard

def findMatch (x : Nat → Nat) (q : Nat) : Nat → Option Nat
  | 0 => none
  | j+1 => if x j = q then some (j+1) else findMatch x q j

/-- The position whose token the network outputs at position `i`. -/
def target (N : Nat) (x : Nat → Nat) (i : Nat) : Nat :=
  let r := min i (N - 1)
  (findMatch x (x i) r).getD r

theorem findMatch_some (x : Nat → Nat) (q : Nat) (r j : Nat) (h : findMatch x q r = some j) :
    1 ≤ j ∧ j ≤ r ∧ x (j - 1) = q ∧ ∀ k, j < k → k ≤ r → x (k - 1) ≠ q := by
  induction r with
  | zero => simp [findMatch] at h
  | succ r ih =>
    simp only [findMatch] at h
    split at h
    · rename_i hx; simp at h; subst h
      refine ⟨by omega, by omega, by simpa using hx, fun k h1 h2 => by omega⟩
    · rename_i hx
      obtain ⟨a, b, c, e⟩ := ih h
      refine ⟨a, by omega, c, fun k h1 h2 => ?_⟩
      by_cases hk : k = r + 1
      · subst hk; simpa using hx
      · exact e k h1 (by omega)

theorem findMatch_none (x : Nat → Nat) (q : Nat) (r : Nat) (h : findMatch x q r = none) :
    ∀ k, 1 ≤ k → k ≤ r → x (k - 1) ≠ q := by
  induction r with
  | zero => intro k h1 h2; omega
  | succ r ih =>
    simp only [findMatch] at h
    split at h
    · simp at h
    · rename_i hx
      intro k h1 h2
      by_cases hk : k = r + 1
      · subst hk; simpa using hx
      · exact ih h k h1 (by omega)

theorem findMatch_congr (x y : Nat → Nat) (q : Nat) (r : Nat) (h : ∀ k, k < r → x k = y k) :
    findMatch x q r = findMatch y q r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [findMatch]; rw [h r (by omega), ih (fun k hk => h k (by omega))]

/-- Hypotheses on the head-2 constants under which the law holds. -/
structure LawHyp (N : Nat) (cm : Int) (w : Nat → Int) : Prop where
  two_le : 2 ≤ N
  /-- the ramp is positive inside the window -/
  w1_pos : 0 < w 1
  /-- position 0 is below position 1 -/
  w0_lt : w 0 < w 1
  /-- recency: the ramp is strictly increasing on `1, …, N-1` -/
  mono : ∀ a b, 1 ≤ a → a < b → b < N → w a < w b
  /-- a match anywhere beats a non-match anywhere -/
  match_wins : w (N - 1) < cm + w 1

theorem LawHyp.w_pos {N : Nat} {cm : Int} {w : Nat → Int} (h : LawHyp N cm w) (a : Nat)
    (ha : 1 ≤ a) (haN : a < N) : 0 < w a := by
  by_cases h1 : a = 1
  · subst h1; exact h.w1_pos
  · have := h.mono 1 a (by omega) (by omega) haN; have := h.w1_pos; omega

theorem LawHyp.w_le_top {N : Nat} {cm : Int} {w : Nat → Int} (h : LawHyp N cm w) (a : Nat)
    (ha : 1 ≤ a) (haN : a < N) : w a ≤ w (N - 1) := by
  by_cases h1 : a = N - 1
  · subst h1; exact Int.le_refl _
  · exact Int.le_of_lt (h.mono a (N - 1) ha (by omega) (by omega))

theorem LawHyp.w_ge_one {N : Nat} {cm : Int} {w : Nat → Int} (h : LawHyp N cm w) (a : Nat)
    (ha : 1 ≤ a) (haN : a < N) : w 1 ≤ w a := by
  by_cases h1 : a = 1
  · subst h1; exact Int.le_refl _
  · exact Int.le_of_lt (h.mono 1 a (by omega) (by omega) haN)

theorem prevPos_in {N j : Nat} (h1 : 1 ≤ j) (h2 : j < N) : prevPos N j = j - 1 := by
  unfold prevPos; rw [ite_eq_left ⟨h1, h2⟩]

theorem prevPos_out {N j : Nat} (h : ¬(1 ≤ j ∧ j < N)) : prevPos N j = 0 := by
  unfold prevPos; rw [ite_eq_right h]

/-- **The law.** Under `LawHyp`, head 2 attends to `target`. -/
theorem argmax_score2_eq_target {N : Nat} {cm : Int} {w : Nat → Int} (hw : LawHyp N cm w)
    (x : Nat → Nat) (i : Nat) :
    argmaxUpTo (score2Form N cm w x i) i = target N x i := by
  have hN := hw.two_le
  have hcm : 0 < cm := by
    have := hw.w_ge_one (N - 1) (by omega) (by omega); have := hw.match_wins; omega
  unfold target
  simp only
  generalize hr : min i (N - 1) = r
  have hri : r ≤ i := by omega
  have hrN : r < N := by omega
  cases hf : findMatch x (x i) r with
  | some j =>
    obtain ⟨hj1, hjr, hjm, hlater⟩ := findMatch_some x (x i) r j hf
    simp only [Option.getD_some]
    have hjN : j < N := by omega
    have sj : score2Form N cm w x i j = cm + w j := by
      unfold score2Form; rw [prevPos_in hj1 hjN, ite_eq_left hjm.symm, ite_eq_left hjN]
    apply argmaxUpTo_eq_of_strict _ _ _ (by omega)
    intro k hk hkj
    rw [sj]
    have wj := hw.w_pos j hj1 hjN
    have wj1 := hw.w_ge_one j hj1 hjN
    have top := hw.match_wins
    have w01 := hw.w0_lt
    unfold score2Form
    by_cases hk0 : k = 0
    · subst hk0
      rw [prevPos_out (by omega), ite_eq_left (by omega : (0:Nat) < N)]
      split <;> omega
    by_cases hkN : k < N
    · rw [prevPos_in (by omega) hkN, ite_eq_left hkN]
      have wk := hw.w_le_top k (by omega) hkN
      by_cases hkl : k < j
      · have := hw.mono k j (by omega) hkl hjN
        split <;> omega
      · have hne := hlater k (by omega) (by omega)
        rw [ite_eq_right (fun h => hne h.symm)]
        omega
    · rw [prevPos_out (by omega), ite_eq_right hkN]
      split <;> omega
  | none =>
    have hno := findMatch_none x (x i) r hf
    simp only [Option.getD_none]
    by_cases hr0 : r = 0
    · subst hr0
      have : i = 0 := by omega
      subst this; rfl
    have hx0 : x 0 ≠ x i := by have := hno 1 (by omega) (by omega); simpa using this
    have sr : score2Form N cm w x i r = w r := by
      unfold score2Form
      rw [prevPos_in (by omega) hrN, ite_eq_right (fun h => hno r (by omega) (Nat.le_refl _) h.symm),
        ite_eq_left hrN]; omega
    apply argmaxUpTo_eq_of_strict _ _ _ hri
    intro k hk hkr
    rw [sr]
    have wr := hw.w_pos r (by omega) hrN
    have wr1 := hw.w_ge_one r (by omega) hrN
    have w01 := hw.w0_lt
    unfold score2Form
    by_cases hk0 : k = 0
    · subst hk0
      rw [prevPos_out (by omega), ite_eq_right (fun h => hx0 h.symm),
        ite_eq_left (by omega : (0:Nat) < N)]; omega
    by_cases hkl : k < r
    · rw [prevPos_in (by omega) (by omega), ite_eq_right (fun h => hno k (by omega) (by omega) h.symm),
        ite_eq_left (by omega : k < N)]
      have := hw.mono k r (by omega) hkl hrN; omega
    · -- r < k ≤ i forces r = N - 1, so k is outside the window
      have hkN : ¬ k < N := by omega
      rw [prevPos_out (by omega), ite_eq_right (fun h => hx0 h.symm), ite_eq_right hkN]; omega

/-- Combined with the mechanism: the whole network obeys the law. -/
theorem Spec.predict_law {M : Model} {c1 cm cU : Int} {w : Nat → Int} (hs : Spec M c1 cm cU w)
    (hw : LawHyp M.N cm w) (hc1 : 0 < c1) (hcU : 0 < cU) {x : Nat → Nat} (hx : ∀ k, x k < M.V)
    (i : Nat) : M.predict x i = x (target M.N x i) := by
  rw [hs.predict_formula hx hc1 hcU, argmax_score2_eq_target hw]

theorem Spec.attn2_law {M : Model} {c1 cm cU : Int} {w : Nat → Int} (hs : Spec M c1 cm cU w)
    (hw : LawHyp M.N cm w) (hc1 : 0 < c1) {x : Nat → Nat} (hx : ∀ k, x k < M.V)
    (i : Nat) : M.attn2 x i = target M.N x i := by
  rw [hs.attn2_eq hx hc1, argmax_score2_eq_target hw]

end Whisperheard
