import CKLaneM05.FE8.EAdapt
import CKLaneM05.FE8.SPlane
import CKLaneM05.FE8.W1

/-!
# Lane M05 / FE8: certificate type v3 = v2 (outside, cap, parent, plane, Lane E kernels) + shifted plane

`W3.check_sound : W3.check B w = true → LeafOK B`, no other hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM05.FE8

/-- FE8 certificate, version 3. -/
inductive W3 where
  | old (w : W2)
  | sp (c : SC)
  deriving Repr

def W3.check (B : CKLaneD.Box) : W3 → Bool
  | .old w => W2.check B w
  | .sp c => splaneCheck B c

theorem W3.check_sound : ∀ (B : CKLaneD.Box) (w : W3), W3.check B w = true → LeafOK B
  | B, .old w, h => W2.check_sound B w h
  | _, .sp _, h => leafOK_of_splaneCheck h

end CKLaneM05.FE8

#check @CKLaneM05.FE8.W3.check_sound
#print axioms CKLaneM05.FE8.W3.check_sound
