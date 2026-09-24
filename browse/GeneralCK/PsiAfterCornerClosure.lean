import GeneralCK.PsiAfterTailClosure
import GeneralCK.PsiEndpointBellman
import GeneralCK.PsiOppositeBoundaryOwner
import GeneralCK.PsiOppositeLowEntropyOwner

/-!
# Residual active-psi interface after the analytic endpoint argument

The same-side ratio tail, opposite deterministic corner, opposite boundary,
and global opposite low-entropy region are proved. The successive interfaces
below preserve the earlier APIs; the final interface has three owner fields.
-/

namespace GeneralCK

structure ResidualPsiCertificateOwnersExceptRatioTailCorner : Prop where
  sameChart : SameSidePsiChartOwner
  oppositeCentral : OppositePsiCentralOwner
  oppositeBoundary : OppositePsiBoundaryOwner
  oppositeLowEntropy : OppositePsiLowEntropyOwner
  oppositeCompact : OppositePsiCompactOwner

/-- Restore the previous owner interface using the proved corner inequality.
Keeping this constructor separate preserves the earlier closure APIs. -/
theorem ResidualPsiCertificateOwnersExceptRatioTailCorner.toOwnersExceptRatioTail
    (h : ResidualPsiCertificateOwnersExceptRatioTailCorner) :
    ResidualPsiCertificateOwnersExceptRatioTail where
  sameChart := h.sameChart
  oppositeCentral := h.oppositeCentral
  oppositeBoundary := h.oppositeBoundary
  oppositeCorner := oppositePsiCornerOwner
  oppositeLowEntropy := h.oppositeLowEntropy
  oppositeCompact := h.oppositeCompact

theorem ResidualPsiCertificateOwnersExceptRatioTailCorner.toOwners
    (h : ResidualPsiCertificateOwnersExceptRatioTailCorner) :
    ResidualPsiCertificateOwners :=
  h.toOwnersExceptRatioTail.toOwners

theorem residualPsi_of_certificateOwners_after_ratioTail_corner
    (h : ResidualPsiCertificateOwnersExceptRatioTailCorner) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost :=
  residualPsi_of_certificateOwners_after_ratioTail h.toOwnersExceptRatioTail

/-- Four fields remain after the full opposite boundary is also discharged. -/
structure ResidualPsiCertificateOwnersExceptRatioTailCornerBoundary : Prop where
  sameChart : SameSidePsiChartOwner
  oppositeCentral : OppositePsiCentralOwner
  oppositeLowEntropy : OppositePsiLowEntropyOwner
  oppositeCompact : OppositePsiCompactOwner

theorem ResidualPsiCertificateOwnersExceptRatioTailCornerBoundary.toOwnersExceptRatioTailCorner
    (h : ResidualPsiCertificateOwnersExceptRatioTailCornerBoundary) :
    ResidualPsiCertificateOwnersExceptRatioTailCorner where
  sameChart := h.sameChart
  oppositeCentral := h.oppositeCentral
  oppositeBoundary := oppositePsiBoundaryOwner
  oppositeLowEntropy := h.oppositeLowEntropy
  oppositeCompact := h.oppositeCompact

theorem ResidualPsiCertificateOwnersExceptRatioTailCornerBoundary.toOwnersExceptRatioTail
    (h : ResidualPsiCertificateOwnersExceptRatioTailCornerBoundary) :
    ResidualPsiCertificateOwnersExceptRatioTail :=
  h.toOwnersExceptRatioTailCorner.toOwnersExceptRatioTail

theorem residualPsi_of_certificateOwners_after_endpoint_analytic
    (h : ResidualPsiCertificateOwnersExceptRatioTailCornerBoundary) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost :=
  residualPsi_of_certificateOwners_after_ratioTail h.toOwnersExceptRatioTail

/-- The three active-psi regions remaining after the analytic endpoint and
retained-child arguments. Each field keeps the original exact ledger domain. -/
structure ResidualPsiAnalyticRemainingOwners : Prop where
  sameChart : SameSidePsiChartOwner
  oppositeCentral : OppositePsiCentralOwner
  oppositeCompact : OppositePsiCompactOwner

theorem ResidualPsiAnalyticRemainingOwners.toOwnersExceptRatioTailCornerBoundary
    (h : ResidualPsiAnalyticRemainingOwners) :
    ResidualPsiCertificateOwnersExceptRatioTailCornerBoundary where
  sameChart := h.sameChart
  oppositeCentral := h.oppositeCentral
  oppositeLowEntropy := oppositePsiLowEntropyOwner
  oppositeCompact := h.oppositeCompact

theorem ResidualPsiAnalyticRemainingOwners.toOwnersExceptRatioTail
    (h : ResidualPsiAnalyticRemainingOwners) :
    ResidualPsiCertificateOwnersExceptRatioTail :=
  h.toOwnersExceptRatioTailCornerBoundary.toOwnersExceptRatioTail

theorem residualPsi_of_analytic_remaining_owners
    (h : ResidualPsiAnalyticRemainingOwners) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost :=
  residualPsi_of_certificateOwners_after_ratioTail h.toOwnersExceptRatioTail

end GeneralCK

#print axioms GeneralCK.ResidualPsiCertificateOwnersExceptRatioTailCorner.toOwnersExceptRatioTail
#print axioms GeneralCK.residualPsi_of_certificateOwners_after_ratioTail_corner
#print axioms GeneralCK.residualPsi_of_certificateOwners_after_endpoint_analytic
#print axioms GeneralCK.residualPsi_of_analytic_remaining_owners
