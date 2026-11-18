import Whisperheard

/-!
`lake exe whisperheard 2 0 3 1 2 0 3 3 1`

Runs the real network (dense raw weights, via the verified fast evaluator)
and prints, for every position: the token, where each head attends, the
logits, the prediction, and what the proved law (`predict_whisper`) says.
-/

open Whisperheard

def pad (n : Nat) (s : String) : String := String.ofList (List.replicate (n - s.length) ' ') ++ s

def runOn (xs : List Nat) : IO Unit := do
  let x := stream xs
  let L := xs.length
  let tr := Fast.run whisper x L
  IO.println s!"input: {xs}"
  IO.println "  pos  tok  head1→  head2→            logits  pred  law"
  let mut ok := true
  for i in [0:L] do
    let lg := tr.logits.getD i []
    let p := tr.predict whisper i
    let law := x (target 8 x i)
    if p != law then ok := false
    IO.println s!"{pad 5 (toString i)}{pad 5 (toString (xs.getD i 0))}{pad 8 (toString (tr.attn1 whisper i))}{pad 8 (toString (tr.attn2 whisper i))}{pad 18 (toString lg)}{pad 6 (toString p)}{pad 5 (toString law)}"
  IO.println (if ok then "network = law at every position (as proved: predict_whisper)\n"
    else "MISMATCH (impossible if the proofs check)\n")

/-- Greedy generation with the real network (fast evaluator). -/
def generate (p : List Nat) (k : Nat) : List Nat := Id.run do
  let mut l := p
  for _ in [0:k] do
    let tr := Fast.run whisper (stream l) l.length
    l := l ++ [tr.predict whisper (l.length - 1)]
  return l

def showGen (p : List Nat) : IO Unit := do
  let l := generate p 24
  IO.println s!"greedy generation from {p}:"
  IO.println s!"  {l}"
  IO.println s!"  (provably periodic with period ≤ 4 from position {max (p.length - 1) 8 + 3}: gen_periodic)\n"

def main (args : List String) : IO Unit := do
  let parsed := args.filterMap String.toNat?
  if parsed.length != args.length || parsed.any (· ≥ 4) then
    IO.eprintln "usage: whisperheard TOKEN...   (tokens are 0, 1, 2 or 3)"
    IO.Process.exit 1
  if parsed.isEmpty then
    runOn [2, 0, 3, 1, 2, 0, 3, 3, 1, 2, 1, 0]
    runOn [0, 1, 2, 2, 2, 2, 2, 0, 0, 1]
    showGen [2, 0, 3, 1]
  else
    runOn parsed
    showGen parsed
