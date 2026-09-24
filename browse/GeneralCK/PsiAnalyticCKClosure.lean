import GeneralCK.PsiAfterCornerClosure

/-!
# Direct target connection for the remaining analytic owners

This module connects the completed active-psi regions to the approved
all-dimensions CK statement. The unequal-mean phi inequality and three
remaining psi owners are explicit hypotheses. It does not assert a completed
unconditional CK proof.
-/

namespace GeneralCK

theorem finiteHybridBellman_of_phi_and_remaining_psi
    (hphi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 → candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost)
    (hpsi : ResidualPsiAnalyticRemainingOwners) : FiniteHybridBellman :=
  finiteHybridBellman_of_remaining_regions hphi (residualPsi_of_analytic_remaining_owners hpsi)

/-- The approved target follows once the phi theorem and these three
remaining active-psi owners are supplied. -/
theorem generalCourtadeKumar_of_phi_and_remaining_psi
    (hphi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)),
      μ.a < μ.b → μ.a + μ.b ≤ 1 → candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost)
    (hpsi : ResidualPsiAnalyticRemainingOwners) : GeneralCourtadeKumar :=
  generalCourtadeKumar_of_remaining_regions hphi (residualPsi_of_analytic_remaining_owners hpsi)

end GeneralCK

#print axioms GeneralCK.finiteHybridBellman_of_phi_and_remaining_psi
#print axioms GeneralCK.generalCourtadeKumar_of_phi_and_remaining_psi
