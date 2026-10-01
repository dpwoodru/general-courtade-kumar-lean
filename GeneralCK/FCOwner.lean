import GeneralCK.FCRayMain

/-!
# Lane F-C: the owner, modulo the capped sub-case

`owner_of_capped` reduces
`GeneralCK.OppositeCornerPhiAffineCertificate.CertificateOwner`
to the single remaining sub-case in which the ray construction is out of range,
i.e. `H a ≤ E·(1-2a)/(b-a)`.  Everything else — the boundary face `a + b = 1`
(exact equality, `FCPilot.face_certificate`) and the strict interior with the ray
construction in range (`FCRayMain.ray_certificate`) — is already closed.

Nothing here is renamed, weakened or generalised: the conclusion is the exact
target type and the hypothesis is a strictly smaller region of the same domain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCOwner

open GeneralCK
open GeneralCK.PsiAffineChildCertificate

theorem retainedCutoff_eq : SmallMeanPhiCutoff.retainedCutoff = (1 / 10000 : ℝ) := rfl

/-- **Exact reduction.**  The owner follows from the capped sub-case alone. -/
theorem owner_of_capped
    (h : ∀ a b E : ℝ, 0 < a → a < b → a + b < 1 → 1 / 16 < a + b → 1 / 2 < b →
      a + (1 - b) < SmallMeanPhiCutoff.retainedCutoff → 0 < E → E ≤ (H a + H b) / 2 →
      psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E →
      H a ≤ E * (1 - 2 * a) / (b - a) →
      ∃ (L : EntropySupport a) (R : EntropySupport b),
        OppositeCornerPhiAffineCertificate.certificateInequality L R E) :
    OppositeCornerPhiAffineCertificate.CertificateOwner := by
  apply FCPilot.owner_of_strict_interior
  intro a b E ha hab hlt hlarge hb hcut hE hEcap hactive
  have hcut' : a + (1 - b) < 1 / 10000 := by
    rw [retainedCutoff_eq] at hcut
    exact hcut
  by_cases hray : E * (1 - 2 * a) / (b - a) < H a
  · exact FCRayMain.ray_certificate ha hab hlt hb hcut' hE hEcap hactive hray
  · push_neg at hray
    exact h a b E ha hab hlt hlarge hb hcut hE hEcap hactive hray

#check @owner_of_capped
#print axioms owner_of_capped

end GeneralCK.FCOwner
