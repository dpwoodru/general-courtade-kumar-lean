import GeneralCK.FCCapped
import GeneralCK.FCOwner

/-!
# Lane F-C: the owner, modulo ONE scalar inequality

Combining `FCOwner.owner_of_capped` with `FCCapped.capped_certificate_of_scalar`,
the exact target

  `GeneralCK.OppositeCornerPhiAffineCertificate.CertificateOwner`

now follows from a single scalar inequality on the capped region.  No support
objects, no allocation intervals, no `childFloor` appear in the residue: it is a
statement about `eta`, `F` and `psi` alone.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCOwnerFinal

open GeneralCK

/-- **The lane's residue, in its sharpest compiled form.** -/
theorem owner_of_capped_scalar
    (h : ∀ a b E : ℝ, 0 < a → a < b → a + b < 1 → 1 / 16 < a + b → 1 / 2 < b →
      a + (1 - b) < SmallMeanPhiCutoff.retainedCutoff → 0 < E → E ≤ (H a + H b) / 2 →
      psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E →
      H a ≤ E * (1 - 2 * a) / (b - a) →
      eta E - F (b - a) E ≤ F (1 - a - b) E + psi b (2 * E) / 2) :
    OppositeCornerPhiAffineCertificate.CertificateOwner := by
  apply FCOwner.owner_of_capped
  intro a b E ha hab hlt hlarge hb hcut hE hEcap hactive hcapped
  have hcut' : a + (1 - b) < 1 / 10000 := by
    rw [FCOwner.retainedCutoff_eq] at hcut
    exact hcut
  exact FCCapped.capped_certificate_of_scalar ha hab hlt hb hcut' hE hEcap hactive
    (h a b E ha hab hlt hlarge hb hcut hE hEcap hactive hcapped)

#check @owner_of_capped_scalar
#print axioms owner_of_capped_scalar

end GeneralCK.FCOwnerFinal
