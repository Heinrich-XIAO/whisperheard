/-!
# Integer linear algebra, kernel-friendly

Everything in this project is exact integer arithmetic: no floats, no reals, no
Mathlib. Vectors and matrices are plain functions out of `Nat`; a dimension is
only ever supplied at the point where we sum. Every definition is structurally
recursive so the kernel can evaluate it (`decide +kernel` is used heavily).
-/

namespace Whisperheard

/-- A vector over `Int`. Only the first `d` coordinates are ever read. -/
abbrev Vec := Nat → Int
/-- A matrix over `Int`, `A r c` = row `r`, column `c`. -/
abbrev Mat := Nat → Nat → Int

/-- `sumN n f = f 0 + f 1 + ⋯ + f (n-1)`. -/
def sumN : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n+1, f => sumN n f + f n

def zeroV : Vec := fun _ => 0
def vadd (u v : Vec) : Vec := fun k => u k + v k
def smul (c : Int) (u : Vec) : Vec := fun k => c * u k

infixl:65 " ⊞ " => vadd

def dot (n : Nat) (u v : Vec) : Int := sumN n (fun k => u k * v k)
def mulVec (A : Mat) (n : Nat) (v : Vec) : Vec := fun r => sumN n (fun c => A r c * v c)
def col (A : Mat) (c : Nat) : Vec := fun r => A r c
def row (A : Mat) (r : Nat) : Vec := fun c => A r c
/-- Basis vector. -/
def basis (k : Nat) : Vec := fun r => if r = k then 1 else 0

/-- Matrix product `A * B` with inner dimension `n`. -/
def mmul (A B : Mat) (n : Nat) : Mat := fun r c => sumN n (fun k => A r k * B k c)
def transpose (A : Mat) : Mat := fun r c => A c r

/-- A matrix stored as a list of rows; out-of-range entries are `0`. -/
def ofRows (L : List (List Int)) : Mat := fun r c => (L.getD r []).getD c 0

/-! ## `sumN` lemmas -/

theorem sumN_succ (n : Nat) (f : Nat → Int) : sumN (n+1) f = sumN n f + f n := rfl

theorem sumN_add (n : Nat) (f g : Nat → Int) :
    sumN n (fun k => f k + g k) = sumN n f + sumN n g := by
  induction n with
  | zero => simp [sumN]
  | succ n ih => simp only [sumN, ih]; omega

theorem sumN_congr (n : Nat) (f g : Nat → Int) (h : ∀ k, k < n → f k = g k) :
    sumN n f = sumN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumN]
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]

theorem sumN_eq_zero (n : Nat) (f : Nat → Int) (h : ∀ k, k < n → f k = 0) :
    sumN n f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumN]; rw [ih (fun k hk => h k (by omega)), h n (by omega)]; rfl

theorem sumN_zero (n : Nat) : sumN n (fun _ => 0) = 0 :=
  sumN_eq_zero n _ (fun _ _ => rfl)

theorem sumN_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumN n (fun k => c * f k) = c * sumN n f := by
  induction n with
  | zero => simp [sumN]
  | succ n ih => simp only [sumN, ih, Int.mul_add]

/-- A sum of a function supported at a single index. -/
theorem sumN_single (n : Nat) (f : Nat → Int) (j : Nat) (hj : j < n)
    (h : ∀ k, k < n → k ≠ j → f k = 0) : sumN n f = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [sumN]
    by_cases hjn : j = n
    · subst hjn
      rw [sumN_eq_zero j f (fun k hk => h k (by omega) (by omega))]; simp
    · rw [ih (by omega) (fun k hk hkj => h k (by omega) hkj), h n (by omega) (Ne.symm hjn)]
      simp

theorem sumN_comm (n m : Nat) (f : Nat → Nat → Int) :
    sumN n (fun a => sumN m (fun b => f a b)) = sumN m (fun b => sumN n (fun a => f a b)) := by
  induction n with
  | zero => simp [sumN, sumN_zero]
  | succ n ih => simp only [sumN]; rw [ih, ← sumN_add]

theorem sumN_mul_right (n : Nat) (c : Int) (f : Nat → Int) :
    sumN n (fun k => f k * c) = sumN n f * c := by
  rw [Int.mul_comm, ← sumN_mul_left]; apply sumN_congr; intro k _; exact Int.mul_comm _ _

/-! ## Linearity -/

theorem dot_add_left (n : Nat) (u v w : Vec) : dot n (u ⊞ v) w = dot n u w + dot n v w := by
  unfold dot vadd; rw [← sumN_add]; congr 1; funext k; exact Int.add_mul _ _ _

theorem dot_add_right (n : Nat) (u v w : Vec) : dot n u (v ⊞ w) = dot n u v + dot n u w := by
  unfold dot vadd; rw [← sumN_add]; congr 1; funext k; exact Int.mul_add _ _ _

theorem dot_zero_left (n : Nat) (u : Vec) : dot n zeroV u = 0 := by
  unfold dot zeroV; simp [sumN_zero]

theorem dot_zero_right (n : Nat) (u : Vec) : dot n u zeroV = 0 := by
  unfold dot zeroV; simp [sumN_zero]

theorem dot_smul_left (n : Nat) (c : Int) (u v : Vec) : dot n (smul c u) v = c * dot n u v := by
  unfold dot smul; rw [← sumN_mul_left]; congr 1; funext k; exact Int.mul_assoc _ _ _

theorem dot_smul_right (n : Nat) (c : Int) (u v : Vec) : dot n u (smul c v) = c * dot n u v := by
  unfold dot smul; rw [← sumN_mul_left]; congr 1; funext k
  rw [← Int.mul_assoc, Int.mul_comm (u k) c, Int.mul_assoc]

theorem mulVec_add (A : Mat) (n : Nat) (u v : Vec) :
    mulVec A n (u ⊞ v) = mulVec A n u ⊞ mulVec A n v := by
  funext r; unfold mulVec vadd; rw [← sumN_add]; congr 1; funext k; exact Int.mul_add _ _ _

theorem mulVec_zero (A : Mat) (n : Nat) : mulVec A n zeroV = zeroV := by
  funext r; unfold mulVec zeroV; simp [sumN_zero]

theorem mulVec_smul (A : Mat) (n : Nat) (c : Int) (u : Vec) :
    mulVec A n (smul c u) = smul c (mulVec A n u) := by
  funext r; unfold mulVec smul; rw [← sumN_mul_left]; congr 1; funext k
  rw [← Int.mul_assoc, Int.mul_comm (A r k) c, Int.mul_assoc]

theorem vadd_zero (u : Vec) : u ⊞ zeroV = u := by funext k; simp [vadd, zeroV]
theorem zero_vadd (u : Vec) : zeroV ⊞ u = u := by funext k; simp [vadd, zeroV]

/-- Dot products only see the first `n` coordinates. -/
theorem dot_congr (n : Nat) (u u' v v' : Vec) (hu : ∀ k, k < n → u k = u' k)
    (hv : ∀ k, k < n → v k = v' k) : dot n u v = dot n u' v' := by
  unfold dot; apply sumN_congr; intro k hk; rw [hu k hk, hv k hk]

/-- Applying a matrix to a linear combination of columns of `B`. -/
theorem mulVec_comb (A B : Mat) (d m : Nat) (c : Nat → Int) (k : Nat) :
    mulVec A d (fun r => sumN m (fun a => B r a * c a)) k =
      sumN m (fun a => c a * mulVec A d (col B a) k) := by
  unfold mulVec col
  rw [show (fun r => A k r * sumN m (fun a => B r a * c a)) =
      (fun r => sumN m (fun a => A k r * B r a * c a)) by
    funext r; rw [← sumN_mul_left]; apply sumN_congr; intro a _; grind]
  rw [sumN_comm]; apply sumN_congr; intro a _
  rw [← sumN_mul_left]; apply sumN_congr; intro r _; grind

/-- Dot product of two linear combinations. -/
theorem dot_comb (n m : Nat) (c e : Nat → Int) (f g : Nat → Vec) :
    dot n (fun k => sumN m (fun a => c a * f a k)) (fun k => sumN m (fun b => e b * g b k)) =
      sumN m (fun a => sumN m (fun b => c a * e b * dot n (f a) (g b))) := by
  unfold dot
  rw [show (fun k => sumN m (fun a => c a * f a k) * sumN m (fun b => e b * g b k)) =
      (fun k => sumN m (fun a => sumN m (fun b => c a * e b * (f a k * g b k)))) by
    funext k; rw [← sumN_mul_right]; apply sumN_congr; intro a _
    rw [← sumN_mul_left]; apply sumN_congr; intro b _; grind]
  rw [sumN_comm]; apply sumN_congr; intro a _
  rw [sumN_comm]; apply sumN_congr; intro b _
  rw [← sumN_mul_left]

theorem mulVec_mmul (A B : Mat) (m n : Nat) (v : Vec) :
    mulVec (mmul A B m) n v = mulVec A m (mulVec B n v) := by
  funext r; unfold mulVec mmul
  rw [show (fun c => sumN m (fun k => A r k * B k c) * v c) =
      (fun c => sumN m (fun k => A r k * B k c * v c)) by funext c; rw [← sumN_mul_right]]
  rw [sumN_comm]; apply sumN_congr; intro k _
  rw [← sumN_mul_left]; apply sumN_congr; intro c _; grind

/-- Moving a matrix across a dot product. -/
theorem dot_mulVec_left (R : Mat) (m n : Nat) (x y : Vec) :
    dot n (mulVec R m x) y = dot m x (mulVec (transpose R) n y) := by
  unfold dot mulVec transpose
  rw [show (fun k => sumN m (fun a => R k a * x a) * y k) =
      (fun k => sumN m (fun a => R k a * x a * y k)) by funext k; rw [← sumN_mul_right]]
  rw [sumN_comm]; apply sumN_congr; intro a _
  rw [← sumN_mul_left]; apply sumN_congr; intro k _; grind

/-- `u` and `v` agree on the first `n` coordinates. -/
def EqOn (n : Nat) (u v : Vec) : Prop := ∀ k, k < n → u k = v k

instance (n : Nat) (u v : Vec) : Decidable (EqOn n u v) :=
  inferInstanceAs (Decidable (∀ k, k < n → u k = v k))

theorem mulVec_eqOn (A : Mat) (n : Nat) (u v : Vec) (h : EqOn n u v) :
    mulVec A n u = mulVec A n v := by
  funext r; unfold mulVec; apply sumN_congr; intro k hk; rw [h k hk]

theorem dot_eqOn (n : Nat) (u u' v v' : Vec) (hu : EqOn n u u') (hv : EqOn n v v') :
    dot n u v = dot n u' v' := dot_congr n u u' v v' hu hv

theorem EqOn.refl (n : Nat) (u : Vec) : EqOn n u u := fun _ _ => rfl
theorem EqOn.add {n : Nat} {u u' v v' : Vec} (hu : EqOn n u u') (hv : EqOn n v v') :
    EqOn n (u ⊞ v) (u' ⊞ v') := fun k hk => by simp only [vadd]; rw [hu k hk, hv k hk]

/-- An identity matrix (on the first `n` coordinates) acts as the identity. -/
theorem mulVec_id (I : Mat) (n : Nat) (hI : ∀ a, a < n → ∀ b, b < n → I a b = if a = b then 1 else 0)
    (v : Vec) : EqOn n (mulVec I n v) v := by
  intro a ha
  unfold mulVec
  rw [sumN_single n _ a ha (fun b hb hba => by rw [hI a ha b hb, ite_eq_right (Ne.symm hba)]; simp)]
  rw [hI a ha a ha]; simp

theorem ofRows_out_col (L : List (List Int)) (r c : Nat)
    (h : ∀ row ∈ L, row.length ≤ c) : ofRows L r c = 0 := by
  unfold ofRows
  by_cases hr : r < L.length
  · have hl := h _ (List.getElem_mem hr)
    simp [List.getD, hr]; simp [hl]
  · simp [List.getD]; simp [show L.length ≤ r by omega]

end Whisperheard
