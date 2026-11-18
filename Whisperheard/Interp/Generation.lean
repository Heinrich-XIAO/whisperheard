import Whisperheard.Interp.Whisper

/-!
# Greedy generation: the network as a dynamical system

Feed the network its own predictions. Past position 8 the network becomes a
*fixed map on four tokens*, `F`, determined entirely by the first eight
tokens (`gen_recurrence`). Every orbit of a map on a 4-element set is
eventually periodic with period ≤ 4, so:

**From any prompt, greedy generation becomes periodic with period 1, 2, 3
or 4, at the latest from position `max (|prompt| - 1) 8 + 3`**
(`gen_periodic`).
-/

namespace Whisperheard

/-- Append the network's prediction for the last position. -/
def step (l : List Nat) : List Nat := l ++ [whisper.predict (stream l) (l.length - 1)]

/-- The prompt extended by `k` generated tokens. -/
def gen (p : List Nat) : Nat → List Nat
  | 0 => p
  | k+1 => step (gen p k)

theorem gen_length (p : List Nat) (k : Nat) : (gen p k).length = p.length + k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [gen, step, ih]; omega

theorem getD_append_left (l : List Nat) (a : Nat) (i : Nat) (h : i < l.length) :
    (l ++ [a]).getD i 0 = l.getD i 0 := by
  simp [List.getD, List.getElem?_append_left h]

theorem gen_stable (p : List Nat) (k m i : Nat) (h : i < (gen p k).length) :
    (gen p (k + m)).getD i 0 = (gen p k).getD i 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show k + (m + 1) = (k + m) + 1 by omega]
    simp only [gen, step]
    rw [getD_append_left _ _ _ (by rw [gen_length] at h ⊢; omega), ih]

/-- The generated stream. -/
def G (p : List Nat) (i : Nat) : Nat := (gen p (i + 1)).getD i 0

theorem G_eq (p : List Nat) (hp : p ≠ []) (k i : Nat) (h : i < (gen p k).length) :
    G p i = (gen p k).getD i 0 := by
  unfold G
  have hpl : 0 < p.length := List.length_pos_iff.mpr hp
  by_cases hk : i + 1 ≤ k
  · rw [show k = (i + 1) + (k - (i + 1)) by omega, gen_stable p (i+1) _ i (by rw [gen_length]; omega)]
  · rw [show i + 1 = k + (i + 1 - k) by omega, gen_stable p k _ i h]

theorem stream_gen (p : List Nat) (hp : p ≠ []) (k i : Nat) (h : i < (gen p k).length) :
    stream (gen p k) i = G p i := (G_eq p hp k i h).symm

theorem gen_valid (p : List Nat) (hv : ∀ a ∈ p, a < 4) (k : Nat) : ∀ a ∈ gen p k, a < 4 := by
  induction k with
  | zero => exact hv
  | succ k ih =>
    intro a ha
    simp only [gen, step, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | ha
    · exact ih a ha
    · have sv : Valid (stream (gen p k)) := by
        intro j; unfold stream; rw [List.getD_eq_getElem?_getD]
        cases hj : (gen p k)[j]? with
        | none => simp
        | some b => simp only [Option.getD_some]; exact ih b (List.mem_of_getElem? hj)
      rw [ha, predict_whisper sv]; exact sv _

theorem G_valid (p : List Nat) (hv : ∀ a ∈ p, a < 4) : Valid (G p) := by
  intro i; unfold G; rw [List.getD_eq_getElem?_getD]
  cases hj : (gen p (i+1))[i]? with
  | none => simp
  | some b => simp only [Option.getD_some]; exact gen_valid p hv (i+1) b (List.mem_of_getElem? hj)

/-- After the prompt, each token is the network's prediction on the stream so far. -/
theorem G_succ (p : List Nat) (hv : ∀ a ∈ p, a < 4) (hp : p ≠ []) (i : Nat)
    (hi : p.length ≤ i + 1) : G p (i + 1) = whisper.predict (G p) i := by
  have hk : (gen p (i + 1 - p.length)).length = i + 1 := by rw [gen_length]; omega
  rw [G_eq p hp (i + 1 - p.length + 1) (i + 1) (by rw [gen_length]; omega)]
  simp only [gen, step]
  rw [hk, show i + 1 - 1 = i by omega]
  simp [List.getD, show (gen p (i + 1 - p.length)).length = i + 1 from hk]
  have sv : Valid (stream (gen p (i + 1 - p.length))) := by
    intro j; unfold stream; rw [List.getD_eq_getElem?_getD]
    cases hj : (gen p (i + 1 - p.length))[j]? with
    | none => simp
    | some b => simp only [Option.getD_some]; exact gen_valid p hv _ b (List.mem_of_getElem? hj)
  exact predict_causal sv (G_valid p hv) i (fun k hk' => stream_gen p hp _ k (by omega))

/-- `iter f n t = f (f (⋯ (f t)))`, `n` times. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, t => t
  | n+1, t => f (iter f n t)

theorem iter_add (f : Nat → Nat) (a b t : Nat) : iter f (a + b) t = iter f a (iter f b t) := by
  induction a with
  | zero => simp [iter]
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 by omega]; simp only [iter, ih]

/-- The map that generation follows once past the window. It reads only the
first eight generated tokens. -/
def F (p : List Nat) (t : Nat) : Nat := G p ((findMatch (G p) t 7).getD 7)

theorem F_lt (p : List Nat) (hv : ∀ a ∈ p, a < 4) (t : Nat) : F p t < 4 := G_valid p hv _

/-- **Past the window, generation is a fixed map on tokens.** -/
theorem gen_recurrence (p : List Nat) (hv : ∀ a ∈ p, a < 4) (hp : p ≠ []) (i : Nat)
    (hi : p.length ≤ i + 1) (h8 : 8 ≤ i) : G p (i + 1) = F p (G p i) := by
  rw [G_succ p hv hp i hi, predict_beyond (G_valid p hv) i h8]; rfl

theorem gen_iter (p : List Nat) (hv : ∀ a ∈ p, a < 4) (hp : p ≠ []) (s : Nat)
    (hs1 : p.length ≤ s + 1) (hs8 : 8 ≤ s) (k : Nat) : G p (s + k) = iter (F p) k (G p s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show s + (k + 1) = (s + k) + 1 by omega, gen_recurrence p hv hp _ (by omega) (by omega), ih]
    rfl

/-- A map on `{0,1,2,3}` given by its table. -/
def tab (a0 a1 a2 a3 : Nat) (t : Nat) : Nat := [a0, a1, a2, a3].getD t 0

set_option synthInstance.maxSize 4096 in
/-- Every orbit of every map on four points: after three steps it is periodic
with period at most four. (Checked over all 256 maps and 4 starting points.) -/
theorem four_point_orbits : ∀ a0, a0 < 4 → ∀ a1, a1 < 4 → ∀ a2, a2 < 4 → ∀ a3, a3 < 4 →
    ∀ t, t < 4 → iter (tab a0 a1 a2 a3) (3 + 1) t = iter (tab a0 a1 a2 a3) 3 t ∨
      iter (tab a0 a1 a2 a3) (3 + 2) t = iter (tab a0 a1 a2 a3) 3 t ∨
      iter (tab a0 a1 a2 a3) (3 + 3) t = iter (tab a0 a1 a2 a3) 3 t ∨
      iter (tab a0 a1 a2 a3) (3 + 4) t = iter (tab a0 a1 a2 a3) 3 t := by decide +kernel

theorem iter_eq_tab (f : Nat → Nat) (hf : ∀ t, t < 4 → f t < 4) (n t : Nat) (ht : t < 4) :
    iter f n t = iter (tab (f 0) (f 1) (f 2) (f 3)) n t := by
  have hlt : ∀ m, iter f m t < 4 := by
    intro m; induction m with
    | zero => exact ht
    | succ m ih => exact hf _ ih
  induction n with
  | zero => rfl
  | succ n ih =>
    show f (iter f n t) = tab (f 0) (f 1) (f 2) (f 3) (iter (tab (f 0) (f 1) (f 2) (f 3)) n t)
    rw [← ih]
    have : iter f n t = 0 ∨ iter f n t = 1 ∨ iter f n t = 2 ∨ iter f n t = 3 := by
      have := hlt n; omega
    rcases this with h | h | h | h <;> rw [h] <;> rfl

/-- **Greedy generation is eventually periodic with period 1, 2, 3 or 4.** -/
theorem gen_periodic (p : List Nat) (hv : ∀ a ∈ p, a < 4) (hp : p ≠ []) :
    ∃ q, 1 ≤ q ∧ q ≤ 4 ∧ ∀ j, max (p.length - 1) 8 + 3 ≤ j → G p (j + q) = G p j := by
  have hpl : 0 < p.length := List.length_pos_iff.mpr hp
  let s := max (p.length - 1) 8
  have hs1 : p.length ≤ s + 1 := by omega
  have hs8 : 8 ≤ s := by omega
  have hf : ∀ t, t < 4 → F p t < 4 := fun t _ => F_lt p hv t
  have hq : ∃ q, 1 ≤ q ∧ q ≤ 4 ∧
      iter (tab (F p 0) (F p 1) (F p 2) (F p 3)) (3 + q) (G p s) =
        iter (tab (F p 0) (F p 1) (F p 2) (F p 3)) 3 (G p s) := by
    rcases four_point_orbits _ (hf 0 (by omega)) _ (hf 1 (by omega)) _ (hf 2 (by omega)) _
      (hf 3 (by omega)) _ (G_valid p hv s) with h | h | h | h
    · exact ⟨1, by omega, by omega, h⟩
    · exact ⟨2, by omega, by omega, h⟩
    · exact ⟨3, by omega, by omega, h⟩
    · exact ⟨4, by omega, by omega, h⟩
  obtain ⟨q, hq1, hq4, hq⟩ := hq
  refine ⟨q, hq1, hq4, fun j hj => ?_⟩
  have key : iter (F p) (3 + q) (G p s) = iter (F p) 3 (G p s) := by
    rw [iter_eq_tab _ hf _ _ (G_valid p hv s), iter_eq_tab _ hf _ _ (G_valid p hv s)]; exact hq
  obtain ⟨m, rfl⟩ : ∃ m, j = s + (m + 3) := ⟨j - s - 3, by omega⟩
  rw [show s + (m + 3) + q = s + (m + (3 + q)) by omega, gen_iter p hv hp s hs1 hs8,
    gen_iter p hv hp s hs1 hs8, iter_add (F p) m (3 + q), iter_add (F p) m 3, key]

end Whisperheard
