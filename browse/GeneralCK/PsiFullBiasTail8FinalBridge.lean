import GeneralCK.PsiFullBiasTail8CurrentOwners
import GeneralCK.PsiExtendedRegionClosure
import GeneralCK.FinalAssemblyAfterDiagnosticHybrid

/-!
# Direct final-owner bridge for the current active-Psi frontier

This file isolates the active-Psi dependency from the other production
families.  The three fields in `PsiFullBiasTail8CurrentOwners` are exactly
the current strict residual regions.  All of the regions deleted on the way
back to the canonical active-Psi statement are restored by the checked
analytic theorems in the existing conversion chain.
-/

namespace GeneralCK

/-- Restore the canonical three-chart interface from the exact current
frontier.  Each conversion consumes a previously proved closed region. -/
theorem PsiFullBiasTail8CurrentOwners.toExtendedRemainingOwners
    (h : PsiFullBiasTail8CurrentOwners) : ResidualPsiExtendedRemainingOwners where
  sameChart := sameSidePsiExtendedChartOwner_of_tail16
    (sameSidePsiTail16ChartOwner_of_tail15
      (sameSidePsiTail15ChartOwner_of_tail14Extended h.toTail14Same))
  oppositeCentral := PsiCentralAnalytic.toExtendedCentralOwner
    (PsiEntropy200.toCentralAnalyticOwner
      (PsiEighthBias.toEntropy200CentralOwner
        (PsiSeventhBias.toEighthCentralOwner
          (PsiSixthBias.toSeventhCentralOwner
            (PsiFifthBias.toSixthCentralOwner
              (PsiFifthBiasAutomatic.toFifthCentralOwner
                (PsiQuarterBias.toAutomaticCentralOwner
                  (PsiTwoSeventhsBias.toQuarterCentralOwner
                    (PsiThreeTenthsBias.toTwoSeventhsCentralOwner
                      (PsiThreeTenthsCentralTail40.toThreeTenthsCentralOwner
                        (PsiThreeTenthsCentralTail37.toTail40CentralOwner
                          h.toTail37Central)))))))))))
  oppositeCompact := PsiCompactAnalytic.toExtendedCompactOwner
    (PsiEntropy200.toCompactAnalyticOwner
      (PsiEighthBias.toEntropy200CompactOwner
        (PsiSeventhBias.toEighthCompactOwner
          (PsiSixthBias.toSeventhCompactOwner
            (PsiFifthBias.toSixthCompactOwner
              (PsiFifthBiasAutomatic.toFifthCompactOwner
                (PsiQuarterBias.toAutomaticCompactOwner
                  (PsiTwoSeventhsBias.toQuarterCompactOwner
                    (PsiThreeTenthsBias.toTwoSeventhsCompactOwner
                      h.toThreeTenthsCompact)))))))))

/-- The current three residual owners imply the exact actual-law Psi theorem
used by the final hybrid assembly.  It is stated without importing the much
larger final-assembly closure. -/
theorem residualPsi_of_fullBiasTail8CurrentOwners
    (h : PsiFullBiasTail8CurrentOwners) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 →
      1 / 16 < μ.a + μ.b → 1 / 100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy →
      μ.gap ≤ μ.cost :=
  residualPsi_of_extended_remaining_owners h.toExtendedRemainingOwners

/-- Final-assembly adapter.  Its target is definitionally the preceding
actual-law theorem, so it introduces no additional analytic premise. -/
theorem PsiFullBiasTail8CurrentOwners.toRemainingPsiHybridOwner
    (h : PsiFullBiasTail8CurrentOwners) :
    HybridAfterDiagnostic.RemainingPsiHybridOwner :=
  residualPsi_of_fullBiasTail8CurrentOwners h

#print axioms PsiFullBiasTail8CurrentOwners.toExtendedRemainingOwners
#print axioms residualPsi_of_fullBiasTail8CurrentOwners
#print axioms PsiFullBiasTail8CurrentOwners.toRemainingPsiHybridOwner

end GeneralCK
