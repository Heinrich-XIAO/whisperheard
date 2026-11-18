import Whisperheard.Argmax

/-!
# A two-layer, attention-only, hard-attention transformer

* tokens and positions are `Nat`s; an input is any `x : Nat → Nat`
  (an infinite stream — causality means only `x 0, …, x i` matter at `i`);
* the residual stream lives in `ℤ^d`;
* each layer is one attention head with weight matrices `WQ WK WV WO`;
* attention is causal and hard (first argmax over `0, …, i`);
* there are no MLPs, no LayerNorm, no biases.

The forward pass is written out with no cleverness so that it is obviously
the standard transformer computation. It is a *specification*: evaluating it
directly is hopelessly slow (every coordinate read recomputes everything
upstream). `Whisperheard.Fast` is an array-based evaluator that is proved
equal to it.
-/

namespace Whisperheard

structure Head where
  /-- query/key dimension -/
  dh : Nat
  /-- value dimension -/
  dv : Nat
  WQ : Mat  -- dh × d
  WK : Mat  -- dh × d
  WV : Mat  -- dv × d
  WO : Mat  -- d × dv

structure Model where
  /-- vocabulary size -/
  V : Nat
  /-- context window (number of learned positions) -/
  N : Nat
  /-- residual width -/
  d : Nat
  WE : Mat  -- d × V   token embedding (column per token)
  WP : Mat  -- d × N   positional embedding (column per position)
  WU : Mat  -- V × d   unembedding (row per token)
  h1 : Head
  h2 : Head

namespace Head

/-- Query of a residual vector. -/
def q (h : Head) (d : Nat) (r : Vec) : Vec := mulVec h.WQ d r
/-- Key of a residual vector. -/
def k (h : Head) (d : Nat) (r : Vec) : Vec := mulVec h.WK d r
/-- Attention score between a query residual `a` and a key residual `b`. -/
def qk (h : Head) (d : Nat) (a b : Vec) : Int := dot h.dh (h.q d a) (h.k d b)
/-- What the head writes into the residual stream when it attends to `b`. -/
def ov (h : Head) (d : Nat) (b : Vec) : Vec := mulVec h.WO h.dv (mulVec h.WV d b)

/-- Score of position `i` attending to position `j`. -/
def score (h : Head) (d : Nat) (r : Nat → Vec) (i j : Nat) : Int := h.qk d (r i) (r j)
/-- The (single) position that `i` attends to. -/
def attn (h : Head) (d : Nat) (r : Nat → Vec) (i : Nat) : Nat := argmaxUpTo (h.score d r i) i
/-- The head's output at position `i`. -/
def out (h : Head) (d : Nat) (r : Nat → Vec) (i : Nat) : Vec := h.ov d (r (h.attn d r i))

end Head

namespace Model
variable (M : Model)

/-- Token embedding vector. -/
def tok (t : Nat) : Vec := col M.WE t
/-- Positional embedding vector. -/
def pos (p : Nat) : Vec := col M.WP p

def resid0 (x : Nat → Nat) (i : Nat) : Vec := M.tok (x i) ⊞ M.pos i
def attn1 (x : Nat → Nat) (i : Nat) : Nat := M.h1.attn M.d (M.resid0 x) i
def resid1 (x : Nat → Nat) (i : Nat) : Vec := M.resid0 x i ⊞ M.h1.out M.d (M.resid0 x) i
def attn2 (x : Nat → Nat) (i : Nat) : Nat := M.h2.attn M.d (M.resid1 x) i
def resid2 (x : Nat → Nat) (i : Nat) : Vec := M.resid1 x i ⊞ M.h2.out M.d (M.resid1 x) i
def logits (x : Nat → Nat) (i : Nat) (t : Nat) : Int := dot M.d (row M.WU t) (M.resid2 x i)
/-- Greedy next-token prediction at position `i` (first argmax over the vocabulary). -/
def predict (x : Nat → Nat) (i : Nat) : Nat := argmaxUpTo (M.logits x i) (M.V - 1)

end Model

/-- Turn a finite list into an input stream (padding with token `0`). -/
def stream (l : List Nat) : Nat → Nat := fun i => l.getD i 0

end Whisperheard
