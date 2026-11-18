import Whisperheard
/-! `lake env lean scripts/Audit.lean` — which axioms do the headline results rest on? -/
open Whisperheard Whisperheard.Interp
#print axioms predict_whisper
#print axioms logits_whisper
#print axioms predict_equivariant
#print axioms predict_causal
#print axioms Fast.predict_eq
#print axioms qk1_closed
#print axioms qk2_closed
#print axioms noSuppress_same
#print axioms frontier
#print axioms decompiled_eq
#print axioms head2_unique
#print axioms conj_predict
