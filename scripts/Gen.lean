/-!
# Weight generator (pure Lean, no training)

Run with `lake env lean --run scripts/Gen.lean > Whisperheard/Weights.lean`.

1. Writes down a *clean*, sparse, hand-designed set of weights.
2. Hides them behind random unimodular integer changes of basis — one for the
   residual stream (`U`) and one for each head-internal space. The function
   the network computes is unchanged (that is a theorem: see
   `Whisperheard.Interp.Gauge`), but every raw weight matrix becomes dense and
   unreadable.
3. Prints only the obfuscated weights. Neither `U` nor the clean weights are
   printed anywhere: the interpretability work in `Whisperheard/Interp` has to
   recover all of it from the raw numbers.
-/

abbrev M := Array (Array Int)

def zeros (r c : Nat) : M := Array.replicate r (Array.replicate c 0)
def eye (n : Nat) : M := (List.range n).toArray.map fun i => (List.range n).toArray.map fun j => if i = j then 1 else 0
def get (A : M) (i j : Nat) : Int := (A.getD i #[]).getD j 0
def set (A : M) (i j : Nat) (v : Int) : M := A.modify i (fun r => r.set! j v)
def rows (A : M) : Nat := A.size
def cols (A : M) : Nat := (A.getD 0 #[]).size

def mm (A B : M) : M :=
  (List.range (rows A)).toArray.map fun i => (List.range (cols B)).toArray.map fun j =>
    (List.range (cols A)).foldl (fun acc k => acc + get A i k * get B k j) 0
def tr (A : M) : M :=
  (List.range (cols A)).toArray.map fun i => (List.range (rows A)).toArray.map fun j => get A j i

/-- Deterministic LCG. -/
structure Rng where s : Nat
def Rng.next (g : Rng) : Nat × Rng :=
  let s := (g.s * 6364136223846793005 + 1442695040888963407) % (2^64)
  (s / 65536, ⟨s⟩)

/-- A random unimodular matrix and its exact inverse, built from `ops`
elementary row operations `row i += c * row j` with `c = ±1`, plus a random
signed permutation. -/
def unimodular (n ops : Nat) (g : Rng) : M × M × Rng := Id.run do
  let mut A := eye n
  let mut B := eye n   -- invariant: A * B = I
  let mut g := g
  -- signed permutation first
  for i in [0:n] do
    let (r, g') := g.next; g := g'
    let j := i + r % (n - i)
    -- swap rows i j of A, columns i j of B
    let ai := A[i]!; let aj := A[j]!
    A := (A.set! i aj).set! j ai
    for k in [0:n] do
      let bi := get B k i; let bj := get B k j
      B := set (set B k i bj) k j bi
    let (r2, g'') := g.next; g := g''
    if r2 % 2 = 0 then
      A := A.modify i (·.map (- ·))
      for k in [0:n] do B := set B k i (- get B k i)
  for _ in [0:ops] do
    let (r1, g1) := g.next; let (r2, g2) := g1.next; let (r3, g3) := g2.next
    g := g3
    let i := r1 % n; let j := r2 % n
    if i ≠ j then
      let c : Int := if r3 % 2 = 0 then 1 else -1
      A := A.modify i fun row => (List.range n).toArray.map fun k => row[k]! + c * get A j k
      for k in [0:n] do B := set B k j (get B k j - c * get B k i)
  return (A, B, g)

/-! ## The clean, hand-designed network -/

def d := 20
def V := 4
def N := 8
def c1 : Int := 4    -- head-1 positional sharpness
def cm : Int := 10   -- head-2 match bonus
def cU : Int := 5    -- unembedding gain
def w (p : Nat) : Int := if p = 0 then -10 else p   -- head-2 positional key weight

-- residual layout: tokens 0..3 | positions 4..11 | prev-token 12..15 | output 16..19
def build (r c : Nat) (f : Nat → Nat → Int) : M :=
  (List.range r).toArray.map fun i => (List.range c).toArray.map fun j => f i j

def WE := build d V fun k t => if k = t then 1 else 0
def WP := build d N fun k p => if k = 4 + p then 1 else 0
def WQ1 := build 8 d fun a k => if k = 4 + a then 1 else 0
def WK1 := build 8 d fun a k => if a ≥ 1 ∧ k = 4 + (a - 1) then c1 else 0
def WV1 := build 4 d fun a k => if k = a then 1 else 0
def WO1 := build d 4 fun k a => if k = 12 + a then 1 else 0
def WQ2 := build 5 d fun a k => if a < 4 then (if k = a then 1 else 0) else (if k < 4 then 1 else 0)
def WK2 := build 5 d fun a k =>
  if a < 4 then (if k = 12 + a then cm else 0) else (if 4 ≤ k ∧ k < 12 then w (k - 4) else 0)
def WV2 := build 4 d fun a k => if k = a then 1 else 0
def WO2 := build d 4 fun k a => if k = 16 + a then 1 else 0
def WU := build V d fun t k => if k = 16 + t then cU else 0

def showRow (r : Array Int) : String :=
  "[" ++ ", ".intercalate (r.toList.map fun v => toString v) ++ "]"
def showMat (name : String) (A : M) : String :=
  s!"def {name} : List (List Int) := [\n" ++
    ",\n".intercalate (A.toList.map fun r => "  " ++ showRow r) ++ "]\n"

def maxAbs (A : M) : Int := A.foldl (fun m r => r.foldl (fun m v => max m v.natAbs) m) 0

def main : IO Unit := do
  let g : Rng := ⟨20261118⟩
  let (U, Ui, g) := unimodular d 140 g
  let (R1, R1i, g) := unimodular 8 14 g
  let (A1, A1i, g) := unimodular 4 6 g
  let (R2, R2i, g) := unimodular 5 8 g
  let (A2, A2i, _) := unimodular 4 6 g
  -- sanity: inverses are exact
  for (X, Y) in [(U, Ui), (R1, R1i), (A1, A1i), (R2, R2i), (A2, A2i)] do
    if mm X Y != eye (rows X) then throw <| IO.userError "bad inverse"
  let WE' := mm U WE
  let WP' := mm U WP
  let WQ1' := mm (mm R1 WQ1) Ui
  let WK1' := mm (mm (tr R1i) WK1) Ui
  let WV1' := mm (mm A1 WV1) Ui
  let WO1' := mm (mm U WO1) A1i
  let WQ2' := mm (mm R2 WQ2) Ui
  let WK2' := mm (mm (tr R2i) WK2) Ui
  let WV2' := mm (mm A2 WV2) Ui
  let WO2' := mm (mm U WO2) A2i
  let WU' := mm WU Ui
  let all := [("WE", WE'), ("WP", WP'), ("WQ1", WQ1'), ("WK1", WK1'), ("WV1", WV1'),
    ("WO1", WO1'), ("WQ2", WQ2'), ("WK2", WK2'), ("WV2", WV2'), ("WO2", WO2'), ("WU", WU')]
  IO.eprintln s!"max |entry| per matrix: {all.map fun (n, A) => (n, maxAbs A)}"
  IO.println "import Whisperheard.Model

/-!
# The raw weights of `whisper`

Generated by `scripts/Gen.lean` (deterministic, seeded). No training was
involved. These are the *only* numbers that define the network; everything in
`Whisperheard/Interp` is derived from them.

Shapes (rows × columns): `WE` 20×4, `WP` 20×8, `WQ1 WK1` 8×20, `WV1` 4×20,
`WO1` 20×4, `WQ2 WK2` 5×20, `WV2` 4×20, `WO2` 20×4, `WU` 4×20.
-/

namespace Whisperheard.Weights
"
  for (n, A) in all do IO.println (showMat n A)
  IO.println "end Whisperheard.Weights

namespace Whisperheard
open Weights

/-- The network. Vocabulary `4`, context window `8`, residual width `20`. -/
def whisper : Model where
  V := 4
  N := 8
  d := 20
  WE := ofRows WE
  WP := ofRows WP
  WU := ofRows WU
  h1 := { dh := 8, dv := 4, WQ := ofRows WQ1, WK := ofRows WK1, WV := ofRows WV1, WO := ofRows WO1 }
  h2 := { dh := 5, dv := 4, WQ := ofRows WQ2, WK := ofRows WK2, WV := ofRows WV2, WO := ofRows WO2 }

end Whisperheard"
