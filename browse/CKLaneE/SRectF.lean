import CKLaneE.SRectC

/-!
# Lane E: batched archived-leaf families per certified rectangle

`family_of_all`: a certified rectangle `RectOK X t0` and one kernel-checked Boolean
`L.all (fun p => fitsC (sBoxL p) X t0)` give `LeafS (sBoxL p)` for every path `p ∈ L`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.S

theorem family_of_all {X : SRect} {t0 : ℚ} (hR : RectOK X t0) (L : List (List ℕ))
    (h : L.all (fun p => fitsC (sBoxL p) X t0) = true) : ∀ p ∈ L, LeafS (sBoxL p) := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  exact leafS_of_rectC (sBoxL p) hR this

end CKLaneE.S

#print axioms CKLaneE.S.family_of_all
