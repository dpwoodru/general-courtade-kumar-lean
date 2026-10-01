import GeneralCK.SmallMeanRegion
import GeneralCK.LowInformationRegion
import GeneralCK.ConditionalCK
import GeneralCK.EqualMean

namespace GeneralCK

/-- Exact remaining regional premises after removing equal means and the two proved psi regions.
The unequal-mean phi theorem and remaining psi region are explicit hypotheses. -/
theorem finiteHybridBellman_of_remaining_regions
    (hphi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b → μ.a+μ.b ≤ 1 →
      candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b → μ.a+μ.b ≤ 1 →
      1/16 < μ.a+μ.b → 1/100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost) :
    FiniteHybridBellman := by
  apply finiteHybridBellman_of_canonical
  intro k μ hab hsum
  rcases hab.eq_or_lt with heq | hab'
  · exact μ.equal_mean_hybrid heq
  by_cases hphiActive : psi μ.midpoint μ.meanEntropy ≤ phi μ.midpoint μ.meanEntropy
  · exact (hybrid_gap_le_phi hphiActive).trans (hphi k μ hab' hsum)
  have hactive := lt_of_not_ge hphiActive
  by_cases hsmall : μ.a+μ.b ≤ 1/16
  · exact small_mean_hybrid_of_active_psi μ hab hsmall hactive.le
  · by_cases hlow : μ.information ≤ 1/100
    · exact low_information_hybrid_of_active_psi μ hlow hactive.le
    · exact hpsi k μ hab' hsum (lt_of_not_ge hsmall) (lt_of_not_ge hlow) hactive

/-- The approved all-dimensions CK target from the still-open phi and residual psi inputs.
This is a conditional theorem, not an unconditional proof of general CK. -/
theorem generalCourtadeKumar_of_remaining_regions
    (hphi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b → μ.a+μ.b ≤ 1 →
      candidateGap phi μ.a μ.b μ.e μ.f ≤ μ.cost)
    (hpsi : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a < μ.b → μ.a+μ.b ≤ 1 →
      1/16 < μ.a+μ.b → 1/100 < μ.information →
      phi μ.midpoint μ.meanEntropy < psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost) :
    GeneralCourtadeKumar :=
  generalCourtadeKumar_of_finiteHybridBellman (finiteHybridBellman_of_remaining_regions hphi hpsi)

end GeneralCK
