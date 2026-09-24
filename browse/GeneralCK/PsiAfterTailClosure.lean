import GeneralCK.PsiSameRatioTail

/-! The exact residual active-psi interface after the uniform ratio tail. -/

namespace GeneralCK

/-- Six mathematical owners remain after the completed same-side ratio tail.
These fields retain their exact domains from `PsiRegionLedger`. -/
structure ResidualPsiCertificateOwnersExceptRatioTail : Prop where
  sameChart : SameSidePsiChartOwner
  oppositeCentral : OppositePsiCentralOwner
  oppositeBoundary : OppositePsiBoundaryOwner
  oppositeCorner : OppositePsiCornerOwner
  oppositeLowEntropy : OppositePsiLowEntropyOwner
  oppositeCompact : OppositePsiCompactOwner

theorem ResidualPsiCertificateOwnersExceptRatioTail.toOwners
    (h : ResidualPsiCertificateOwnersExceptRatioTail) :
    ResidualPsiCertificateOwners where
  sameRatioTail := sameSidePsiRatioTailOwner
  sameChart := h.sameChart
  oppositeCentral := h.oppositeCentral
  oppositeBoundary := h.oppositeBoundary
  oppositeCorner := h.oppositeCorner
  oppositeLowEntropy := h.oppositeLowEntropy
  oppositeCompact := h.oppositeCompact

theorem residualPsi_of_certificateOwners_after_ratioTail
    (h : ResidualPsiCertificateOwnersExceptRatioTail) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost :=
  residualPsi_of_certificateOwners h.toOwners

#print axioms ResidualPsiCertificateOwnersExceptRatioTail.toOwners
#print axioms residualPsi_of_certificateOwners_after_ratioTail

end GeneralCK
