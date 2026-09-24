import GeneralCK.FCCappedScalar

/-!
# Lane F-C: exact-type closure check

`exact_target` is stated with the target's type written out by NAME, so that a
mismatch between what this lane proved and
`GeneralCK.OppositeCornerPhiAffineCertificate.CertificateOwner`
would be a type error rather than a prose claim.

`exact_target_unfolded` writes the SAME proposition out in full, exactly as it
appears at `GeneralCK/OppositeCornerPhiAffineCertificate.lean:28-34`, and is
inhabited by the same term.  If the definition on disk differed from the one
this lane reduced, this declaration would not elaborate.

`downstream_owner` discharges the consumer the corpus actually wants,
`FinalProductionAssemblyPositiveCutoff.OppositeCornerBelowCutoffPhiHybridOwner`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCFinalCheck

open GeneralCK

/-- The exact target, by name. -/
theorem exact_target : OppositeCornerPhiAffineCertificate.CertificateOwner :=
  FCCappedScalar.certificate_owner

/-- The exact target, written out in full. -/
theorem exact_target_unfolded :
    ∀ a b E : ℝ, 0 < a → a < b → a + b ≤ 1 → 1 / 16 < a + b → 1 / 2 < b →
      a + (1 - b) < SmallMeanPhiCutoff.retainedCutoff → 0 < E → E ≤ (H a + H b) / 2 →
      psi ((a + b) / 2) E ≤ phi ((a + b) / 2) E →
      ∃ (L : PsiAffineChildCertificate.EntropySupport a)
        (R : PsiAffineChildCertificate.EntropySupport b),
        OppositeCornerPhiAffineCertificate.certificateInequality L R E :=
  FCCappedScalar.certificate_owner

/-- The consumer the corpus wants. -/
theorem downstream_owner :
    FinalProductionAssemblyPositiveCutoff.OppositeCornerBelowCutoffPhiHybridOwner :=
  OppositeCornerPhiAffineCertificate.toOppositeCornerBelowCutoffPhiHybridOwner
    FCCappedScalar.certificate_owner

#check @exact_target
#check @exact_target_unfolded
#check @downstream_owner
#print axioms exact_target
#print axioms exact_target_unfolded
#print axioms downstream_owner

end GeneralCK.FCFinalCheck
