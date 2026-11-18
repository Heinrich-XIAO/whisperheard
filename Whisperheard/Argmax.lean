import Whisperheard.Basic

/-!
# Hard attention: the first argmax

Attention in this project is *hard*: a query attends to exactly one key, the
one with the highest score; among equal scores the **earliest** key wins.
(The model never actually produces a tie at a decisive spot inside the
context window — see `Whisperheard.Interp.Margins` — so in-window behaviour
does not depend on this convention. Outside the window it does, and we say
exactly how.)

The argmax is computed by a single left-to-right pass carrying
`(index, score)`, so the kernel evaluates each score once per step.
-/

namespace Whisperheard

/-- `(index, value)` of the first maximum of `s` over `0, …, i`. -/
def argmaxAux (s : Nat → Int) : Nat → Nat × Int
  | 0 => (0, s 0)
  | i+1 =>
    match argmaxAux s i with
    | (a, v) => if v < s (i+1) then (i+1, s (i+1)) else (a, v)

/-- The first index in `0, …, i` maximising `s`. -/
def argmaxUpTo (s : Nat → Int) (i : Nat) : Nat := (argmaxAux s i).1

theorem argmaxAux_succ (s : Nat → Int) (i : Nat) :
    argmaxAux s (i+1) =
      if (argmaxAux s i).2 < s (i+1) then (i+1, s (i+1)) else argmaxAux s i := by
  show (match argmaxAux s i with
    | (a, v) => if v < s (i+1) then (i+1, s (i+1)) else (a, v)) = _
  cases argmaxAux s i; rfl

theorem argmaxAux_snd (s : Nat → Int) (i : Nat) :
    (argmaxAux s i).2 = s (argmaxAux s i).1 := by
  induction i with
  | zero => rfl
  | succ i ih => rw [argmaxAux_succ]; split <;> simp_all

/-- Unfolding one step of `argmaxUpTo`. -/
theorem argmaxUpTo_succ (s : Nat → Int) (i : Nat) :
    argmaxUpTo s (i+1) =
      if s (argmaxUpTo s i) < s (i+1) then i+1 else argmaxUpTo s i := by
  unfold argmaxUpTo
  rw [argmaxAux_succ, argmaxAux_snd]
  split <;> rfl

theorem argmaxUpTo_zero (s : Nat → Int) : argmaxUpTo s 0 = 0 := rfl

theorem argmaxUpTo_le (s : Nat → Int) (i : Nat) : argmaxUpTo s i ≤ i := by
  induction i with
  | zero => simp [argmaxUpTo_zero]
  | succ i ih => rw [argmaxUpTo_succ]; split <;> omega

/-- The selected index is a maximum. -/
theorem le_argmaxUpTo (s : Nat → Int) (i j : Nat) (hj : j ≤ i) :
    s j ≤ s (argmaxUpTo s i) := by
  induction i with
  | zero => have : j = 0 := by omega
            subst this; simp [argmaxUpTo_zero]
  | succ i ih =>
    rw [argmaxUpTo_succ]
    by_cases hji : j = i + 1
    · subst hji; split <;> omega
    · have := ih (by omega); split <;> omega

/-- Everything strictly before the selected index scores strictly less. -/
theorem lt_of_lt_argmaxUpTo (s : Nat → Int) (i k : Nat) (hk : k < argmaxUpTo s i) :
    s k < s (argmaxUpTo s i) := by
  induction i with
  | zero => simp [argmaxUpTo_zero] at hk
  | succ i ih =>
    rw [argmaxUpTo_succ] at hk ⊢
    split
    · rename_i h
      have := le_argmaxUpTo s i k (by have := argmaxUpTo_le s i; split at hk <;> omega)
      omega
    · rename_i h; simp [h] at hk; exact ih hk

/-- Characterisation: `j` is selected iff it is a maximum and every earlier
index is strictly worse. -/
theorem argmaxUpTo_eq (s : Nat → Int) (i j : Nat) (hj : j ≤ i)
    (hmax : ∀ k, k ≤ i → s k ≤ s j) (hfirst : ∀ k, k < j → s k < s j) :
    argmaxUpTo s i = j := by
  have h1 := le_argmaxUpTo s i j hj
  have h2 := hmax _ (argmaxUpTo_le s i)
  rcases Nat.lt_trichotomy (argmaxUpTo s i) j with h | h | h
  · have := hfirst _ h; omega
  · exact h
  · have := lt_of_lt_argmaxUpTo s i j h; omega

/-- Strict unique maximum ⇒ selected (tie-breaking irrelevant). -/
theorem argmaxUpTo_eq_of_strict (s : Nat → Int) (i j : Nat) (hj : j ≤ i)
    (h : ∀ k, k ≤ i → k ≠ j → s k < s j) : argmaxUpTo s i = j := by
  apply argmaxUpTo_eq s i j hj
  · intro k hk; by_cases hkj : k = j
    · subst hkj; exact Int.le_refl _
    · exact Int.le_of_lt (h k hk hkj)
  · intro k hk; exact h k (by omega) (by omega)

theorem argmaxUpTo_congr (s t : Nat → Int) (i : Nat) (h : ∀ k, k ≤ i → s k = t k) :
    argmaxUpTo s i = argmaxUpTo t i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [argmaxUpTo_succ, argmaxUpTo_succ, ih (fun k hk => h k (by omega))]
    rw [h (i+1) (Nat.le_refl _), h (argmaxUpTo t i) (by have := argmaxUpTo_le t i; omega)]

/-- If every score is equal, the first index wins. -/
theorem argmaxUpTo_const (s : Nat → Int) (i : Nat) (c : Int) (h : ∀ k, k ≤ i → s k = c) :
    argmaxUpTo s i = 0 := by
  apply argmaxUpTo_eq s i 0 (Nat.zero_le _)
  · intro k hk; rw [h k hk, h 0 (Nat.zero_le _)]; exact Int.le_refl _
  · intro k hk; omega

end Whisperheard
