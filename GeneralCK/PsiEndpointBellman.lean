import GeneralCK.PsiEndpointPlaneGlobal
import GeneralCK.PsiLargerEntropyLaw
import GeneralCK.PsiOppositeCornerDomain
import GeneralCK.PsiRegionLedger

/-!
# Analytic active-psi Bellman inequality and the complete opposite corner

The supporting plane and retained child comparison now give the actual law
inequality. No endpoint-cost input or numerical certificate is required.
-/

namespace GeneralCK.PsiEndpointBellman

theorem law_gap_margin {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 1 / 80)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a)
    (hqsmall : 1 - μ.a - μ.b ≤ 1 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap + (9 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) ≤ μ.cost :=
  (PsiLargerEntropyLaw.law_gap_margin_of_active μ hsum hEi hd hqsmall hactive).trans
    (PsiEndpointPlane.law_endpoint_logarithmic_lower μ hd)

theorem law_gap_le_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    (hsum : μ.a + μ.b ≤ 1) (hEi : μ.meanEntropy ≤ 1 / 80)
    (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a)
    (hqsmall : 1 - μ.a - μ.b ≤ 1 / 10)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  have hm : 0 ≤ (9 / 100) * ((1 - μ.a - μ.b) ^ 2 / μ.meanEntropy) := by positivity
  have h := law_gap_margin μ hsum hEi hd hqsmall hactive
  linarith

end GeneralCK.PsiEndpointBellman

namespace GeneralCK

/-- The full deterministic opposite-corner owner, derived analytically for
actual finite laws and every positive child entropy allocation. -/
theorem oppositePsiCornerOwner : OppositePsiCornerOwner := by
  intro k μ _hab hsum _hmean _hinfo _hside hc hactive
  obtain ⟨_hq, hqsmall, _hE, hEi, hd, _ha, _hb⟩ :=
    PsiOppositeCornerDomain.corner_domain μ hsum hc
  exact PsiEndpointBellman.law_gap_le_cost μ hsum (by linarith) hd hqsmall hactive.le

end GeneralCK

#print axioms GeneralCK.PsiEndpointBellman.law_gap_margin
#print axioms GeneralCK.PsiEndpointBellman.law_gap_le_cost
#print axioms GeneralCK.oppositePsiCornerOwner
