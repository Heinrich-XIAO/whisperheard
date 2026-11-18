import Whisperheard.Model

/-!
# A fast evaluator, proved equal to the specification

`Model.predict` is a clean mathematical definition but recomputes everything
on every coordinate read. `Fast.run` computes each residual vector, query,
key and value exactly once, as a list, and is proved to agree with the
specification: `Fast.predict_eq`.

Fast-path values are concrete lists; `ofL` turns one back into a `Vec`.
-/

namespace Whisperheard.Fast

def toL (n : Nat) (v : Vec) : List Int := (List.range n).map v
def ofL (l : List Int) : Vec := fun k => l.getD k 0

theorem getD_map_range {α : Type} (n : Nat) (f : Nat → α) (dflt : α) (k : Nat) (hk : k < n) :
    ((List.range n).map f).getD k dflt = f k := by
  simp [List.getD, hk]

theorem ofL_toL (n : Nat) (v : Vec) (k : Nat) (hk : k < n) : ofL (toL n v) k = v k :=
  getD_map_range n v 0 k hk

/-- One attention head applied to cached residuals `R` (one list per position). -/
structure HeadRun where
  qs : List (List Int)
  ks : List (List Int)
  vals : List (List Int)

def runHead (h : Head) (d L : Nat) (R : List (List Int)) : HeadRun :=
  { qs := (List.range L).map fun i => toL h.dh (mulVec h.WQ d (ofL (R.getD i [])))
    ks := (List.range L).map fun i => toL h.dh (mulVec h.WK d (ofL (R.getD i [])))
    vals := (List.range L).map fun i =>
      toL d (mulVec h.WO h.dv (ofL (toL h.dv (mulVec h.WV d (ofL (R.getD i []))))) ) }

def HeadRun.score (hr : HeadRun) (dh : Nat) (i j : Nat) : Int :=
  dot dh (ofL (hr.qs.getD i [])) (ofL (hr.ks.getD j []))

def HeadRun.attn (hr : HeadRun) (dh : Nat) (i : Nat) : Nat := argmaxUpTo (hr.score dh i) i

/-- New residuals after adding the head's output. -/
def HeadRun.next (hr : HeadRun) (dh d L : Nat) (R : List (List Int)) : List (List Int) :=
  (List.range L).map fun i => toL d (ofL (R.getD i []) ⊞ ofL (hr.vals.getD (hr.attn dh i) []))

structure Trace where
  r0 : List (List Int)
  h1 : HeadRun
  r1 : List (List Int)
  h2 : HeadRun
  r2 : List (List Int)
  logits : List (List Int)

/-- Run the whole network on positions `0, …, L-1` of `x`. -/
def run (M : Model) (x : Nat → Nat) (L : Nat) : Trace :=
  let r0 := (List.range L).map fun i => toL M.d (M.tok (x i) ⊞ M.pos i)
  let h1 := runHead M.h1 M.d L r0
  let r1 := h1.next M.h1.dh M.d L r0
  let h2 := runHead M.h2 M.d L r1
  let r2 := h2.next M.h2.dh M.d L r1
  let lg := (List.range L).map fun i => toL M.V fun t => dot M.d (row M.WU t) (ofL (r2.getD i []))
  { r0, h1, r1, h2, r2, logits := lg }

def Trace.attn1 (tr : Trace) (M : Model) (i : Nat) : Nat := tr.h1.attn M.h1.dh i
def Trace.attn2 (tr : Trace) (M : Model) (i : Nat) : Nat := tr.h2.attn M.h2.dh i
def Trace.predict (tr : Trace) (M : Model) (i : Nat) : Nat :=
  argmaxUpTo (fun t => (tr.logits.getD i []).getD t 0) (M.V - 1)

/-! ## Correctness -/

/-- A cached residual list `R` represents the residual function `r` on `0, …, L-1`. -/
def Rep (d L : Nat) (R : List (List Int)) (r : Nat → Vec) : Prop :=
  ∀ i, i < L → EqOn d (ofL (R.getD i [])) (r i)

theorem runHead_score (h : Head) (d L : Nat) (R : List (List Int)) (r : Nat → Vec)
    (hR : Rep d L R r) (i j : Nat) (hi : i < L) (hj : j < L) :
    (runHead h d L R).score h.dh i j = h.score d r i j := by
  unfold HeadRun.score Head.score Head.qk Head.q Head.k runHead
  simp only
  rw [getD_map_range _ _ _ _ hi, getD_map_range _ _ _ _ hj]
  apply dot_eqOn
  · intro k hk; rw [ofL_toL _ _ _ hk, mulVec_eqOn _ _ _ _ (hR i hi)]
  · intro k hk; rw [ofL_toL _ _ _ hk, mulVec_eqOn _ _ _ _ (hR j hj)]

theorem runHead_attn (h : Head) (d L : Nat) (R : List (List Int)) (r : Nat → Vec)
    (hR : Rep d L R r) (i : Nat) (hi : i < L) :
    (runHead h d L R).attn h.dh i = h.attn d r i := by
  unfold HeadRun.attn Head.attn
  apply argmaxUpTo_congr
  intro k hk; exact runHead_score h d L R r hR i k hi (by omega)

theorem runHead_next (h : Head) (d L : Nat) (R : List (List Int)) (r : Nat → Vec)
    (hR : Rep d L R r) :
    Rep d L ((runHead h d L R).next h.dh d L R) (fun i => r i ⊞ h.out d r i) := by
  intro i hi k hk
  unfold HeadRun.next
  rw [getD_map_range _ _ _ _ hi, ofL_toL _ _ _ hk]
  have ha := runHead_attn h d L R r hR i hi
  have hal : h.attn d r i < L := by
    have := argmaxUpTo_le (h.score d r i) i; unfold Head.attn; omega
  unfold vadd Head.out Head.ov
  rw [hR i hi k hk, ha]
  congr 1
  show ofL ((List.range L).map _ |>.getD _ []) k = _
  rw [getD_map_range _ _ _ _ hal, ofL_toL _ _ _ hk]
  rw [mulVec_eqOn h.WV d _ _ (hR _ hal)]
  rw [mulVec_eqOn h.WO h.dv _ _ (fun c hc => ofL_toL _ _ _ hc)]

theorem run_r0 (M : Model) (x : Nat → Nat) (L : Nat) : Rep M.d L (run M x L).r0 (M.resid0 x) := by
  intro i hi k hk
  simp only [run]
  rw [getD_map_range _ _ _ _ hi, ofL_toL _ _ _ hk]; rfl

theorem run_r1 (M : Model) (x : Nat → Nat) (L : Nat) : Rep M.d L (run M x L).r1 (M.resid1 x) :=
  runHead_next M.h1 M.d L _ _ (run_r0 M x L)

theorem run_r2 (M : Model) (x : Nat → Nat) (L : Nat) : Rep M.d L (run M x L).r2 (M.resid2 x) :=
  runHead_next M.h2 M.d L _ _ (run_r1 M x L)

theorem attn1_eq (M : Model) (x : Nat → Nat) (L i : Nat) (hi : i < L) :
    (run M x L).attn1 M i = M.attn1 x i :=
  runHead_attn M.h1 M.d L _ _ (run_r0 M x L) i hi

theorem attn2_eq (M : Model) (x : Nat → Nat) (L i : Nat) (hi : i < L) :
    (run M x L).attn2 M i = M.attn2 x i :=
  runHead_attn M.h2 M.d L _ _ (run_r1 M x L) i hi

theorem logits_eq (M : Model) (x : Nat → Nat) (L i t : Nat) (hi : i < L) (ht : t < M.V) :
    ((run M x L).logits.getD i []).getD t 0 = M.logits x i t := by
  simp only [run]
  rw [getD_map_range _ _ _ _ hi]; unfold toL; rw [getD_map_range _ _ _ _ ht]
  unfold Model.logits
  apply dot_eqOn _ _ _ _ _ (fun _ _ => rfl)
  exact run_r2 M x L i hi

theorem predict_eq (M : Model) (x : Nat → Nat) (L i : Nat) (hi : i < L) (hV : 0 < M.V) :
    (run M x L).predict M i = M.predict x i := by
  unfold Trace.predict Model.predict
  apply argmaxUpTo_congr
  intro t ht; exact logits_eq M x L i t hi (by omega)

end Whisperheard.Fast
