import Whisperheard

/-!
# Basis discovery (pure Lean)

Run with `lake env lean --run scripts/Discover.lean > Whisperheard/Interp/BasisData.lean`.

Uses *only* the raw weights of `whisper`. It collects the 20 candidate
feature directions

  `T 0..3` (token embeddings), `P 0..7` (positional embeddings),
  `S 0..3 = OV₁(T t)` (head-1 writes), `O 0..3 = OV₂(T t)` (head-2 writes),

as the columns of a 20×20 matrix `B`, inverts it exactly over ℚ by
Gauss–Jordan elimination, checks that the inverse is integral, and prints it.
The printed inverse is only a *certificate*: `Whisperheard.Interp.Basis`
re-checks `B⁻¹ B = B B⁻¹ = I` in the kernel.
-/

open Whisperheard

/-- Minimal exact rationals. -/
structure Q where
  n : Int
  d : Nat
deriving BEq, Inhabited

def Q.norm (n : Int) (d : Nat) : Q :=
  let g := Nat.gcd n.natAbs d
  if g = 0 then ⟨0, 1⟩ else ⟨n / g, d / g⟩
def Q.ofInt (n : Int) : Q := ⟨n, 1⟩
instance : Add Q := ⟨fun a b => Q.norm (a.n * b.d + b.n * a.d) (a.d * b.d)⟩
instance : Sub Q := ⟨fun a b => Q.norm (a.n * b.d - b.n * a.d) (a.d * b.d)⟩
instance : Mul Q := ⟨fun a b => Q.norm (a.n * b.n) (a.d * b.d)⟩
def Q.inv (a : Q) : Q := if a.n < 0 then Q.norm (-(a.d : Int)) a.n.natAbs else Q.norm a.d a.n.natAbs
def Q.isZero (a : Q) : Bool := a.n == 0

def bcol (a : Nat) : Vec :=
  if a < 4 then whisper.tok a
  else if a < 12 then whisper.pos (a - 4)
  else if a < 16 then whisper.h1.ov 20 (whisper.tok (a - 12))
  else whisper.h2.ov 20 (whisper.tok (a - 16))

def invert (A : Array (Array Q)) : Option (Array (Array Q)) := Id.run do
  let n := A.size
  let mut M : Array (Array Q) := (List.range n).toArray.map fun i =>
    A[i]! ++ (List.range n).toArray.map fun j => if i = j then Q.ofInt 1 else Q.ofInt 0
  for c in [0:n] do
    let mut piv := n
    for r in [c:n] do
      if piv == n && !(M[r]![c]!).isZero then piv := r
    if piv == n then return none
    let tmp := M[c]!; M := (M.set! c M[piv]!).set! piv tmp
    let inv := (M[c]![c]!).inv
    M := M.set! c (M[c]!.map (· * inv))
    for r in [0:n] do
      if r != c then
        let f := M[r]![c]!
        if !f.isZero then
          let rowc := M[c]!
          M := M.set! r ((List.range (2*n)).toArray.map fun k => M[r]![k]! - f * rowc[k]!)
  return some (M.map fun row => row.extract n (2*n))

def main : IO Unit := do
  let B : Array (Array Q) := (List.range 20).toArray.map fun r =>
    (List.range 20).toArray.map fun a => Q.ofInt (bcol a r)
  match invert B with
  | none => throw <| IO.userError "the 20 candidate directions are linearly dependent"
  | some Bi =>
    if Bi.any (·.any (·.d != 1)) then
      throw <| IO.userError "inverse is not integral: directions are a ℚ-basis but not a ℤ-basis"
    IO.println "/-! Certificate produced by `scripts/Discover.lean`: the inverse of the
discovered basis matrix. Checked in the kernel by `Whisperheard.Interp.Basis`. -/

namespace Whisperheard.Interp

def BinvRows : List (List Int) := ["
    let rows := Bi.toList.map fun row => "  [" ++ ", ".intercalate (row.toList.map (toString ·.n)) ++ "]"
    IO.println (",\n".intercalate rows ++ "]")
    IO.println "\nend Whisperheard.Interp"
