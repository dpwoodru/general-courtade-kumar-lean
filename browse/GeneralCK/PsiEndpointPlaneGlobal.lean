import GeneralCK.PsiEndpointPlaneMinimum
import GeneralCK.PsiEndpointPlaneStationary
import GeneralCK.PsiEndpointPlaneCoordinates
import GeneralCK.PsiEndpointPlaneCoefficients
import GeneralCK.PsiEndpointPlaneLaw

/-!
# The global endpoint supporting plane

The quotient attains an interior minimum. Its two stationary contact
equations have a unique solution. Therefore every prescribed cross-half
contact supplies the global supporting plane and the finite-law cost bound.
-/

namespace GeneralCK.PsiEndpointPlane
open Set

theorem contact_quotient_minimizes {A B x y : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hxy : (x, y) ∈ triangle)
    (h1 : contactLevel1 A B x y = 0) (h0 : contactLevel0 A B x y = 0) :
    ∀ u v : ℝ, 0 < u → u < v → v < 1 →
      quotient A B x y ≤ quotient A B u v := by
  obtain ⟨p, hp, hmin⟩ := quotient_attains_minimum hA hB
  have hmin' : ∀ u v : ℝ, 0 < u → u < v → v < 1 →
      quotient A B p.1 p.2 ≤ quotient A B u v := by
    intro u v hu huv hv
    exact hmin (show (u, v) ∈ triangle from ⟨hu, huv, hv⟩)
  obtain ⟨hp1, hp0⟩ := contactLevels_zero_of_minimum hp.1 hp.2.1 hp.2.2 hmin'
  obtain ⟨hx, hy⟩ := original_contact_system_unique hA.le hB.le (add_pos hA hB)
    hxy hp h1 h0 hp1 hp0
  simpa only [hx, hy] using hmin'

theorem supporting_plane_of_contact {A B x y : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hxy : (x, y) ∈ triangle)
    (h1 : contactLevel1 A B x y = 0) (h0 : contactLevel0 A B x y = 0) :
    ∀ u v : ℝ, 0 < u → u < 1 → 0 < v → v < 1 →
      quotient A B x y * (v - u) ≤
        naturalCost u v + A * Real.binEntropy u + B * Real.binEntropy v := by
  have hmin := contact_quotient_minimizes hA hB hxy h1 h0
  have hC := quotient_pos hA hB hxy.1 hxy.2.1 hxy.2.2
  intro u v hu hu1 hv hv1
  by_cases huv : u < v
  · exact (le_div_iff₀ (sub_pos.mpr huv)).mp (hmin u v hu huv hv1)
  · have hcost := naturalCost_nonneg hu hu1 hv hv1
    have he := mul_nonneg hA.le (Real.binEntropy_nonneg hu.le hu1.le)
    have hf := mul_nonneg hB.le (Real.binEntropy_nonneg hv.le hv1.le)
    have hl : quotient A B x y * (v - u) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hC.le (by linarith)
    linarith

theorem exists_supporting_plane {x y : ℝ}
    (hx : 0 < x) (hx' : x < 1 / 2) (hy : 1 / 2 < y) (hy' : y < 1) :
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧
      (∀ u v : ℝ, 0 < u → u < 1 → 0 < v → v < 1 →
        C * (v - u) ≤ naturalCost u v + A * Real.binEntropy u + B * Real.binEntropy v) ∧
      C * (y - x) = naturalCost x y + A * Real.binEntropy x + B * Real.binEntropy y := by
  obtain ⟨A, B, hA, hB, h1, h0⟩ := exists_positive_contact_coefficients hx hx' hy hy'
  have hxy : (x, y) ∈ triangle := ⟨hx, by linarith, hy'⟩
  refine ⟨A, B, quotient A B x y, hA, hB,
    quotient_pos hA hB hx hxy.2.1 hy', supporting_plane_of_contact hA hB hxy h1 h0, ?_⟩
  exact div_mul_cancel₀ _ (sub_pos.mpr hxy.2.1).ne'

end GeneralCK.PsiEndpointPlane

namespace GeneralCK.PsiEndpointContact.Contact
open PsiEndpointPlane

/-- The strict endpoint contact is a lower bound for every finite interior
law with the same difference and two entropies. No supporting-plane or
stationarity premise remains. -/
theorem value_le_cost {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (c : Contact (μ.b - μ.a) μ.e μ.f) :
    c.value ≤ μ.cost := by
  obtain ⟨A, B, C, _, _, _, hplane, heq⟩ := exists_supporting_plane
    c.left_pos c.left_lt_half
    (show 1 / 2 < 1 - c.right by linarith [c.right_lt_half])
    (show 1 - c.right < 1 by linarith [c.right_pos])
  exact value_le_cost_of_supporting_plane μ c hplane (by
    simpa only [Real.binEntropy_one_sub] using heq)

end GeneralCK.PsiEndpointContact.Contact

#print axioms GeneralCK.PsiEndpointPlane.contact_quotient_minimizes
#print axioms GeneralCK.PsiEndpointPlane.exists_supporting_plane
#print axioms GeneralCK.PsiEndpointContact.Contact.value_le_cost

namespace GeneralCK.PsiEndpointPlane
open PsiSignedSplit

/-- Endpoint entropy-allocation gain for arbitrary feasible interior laws.
All contact existence and global support obligations have been discharged. -/
theorem law_endpoint_logarithmic_lower {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hd : 8 * μ.meanEntropy ≤ μ.b - μ.a) :
    F (μ.b - μ.a) μ.meanEntropy + (μ.b - μ.a) / (2 * Real.log 2) *
      barrier ((μ.e - μ.f) / (μ.e + μ.f)) ≤ μ.cost := by
  have hE : 0 < μ.meanEntropy := by
    unfold InteriorLaw.meanEntropy
    linarith [μ.e_pos, μ.f_pos]
  obtain ⟨c⟩ := PsiEndpointContact.exists_contact_of_feasible
    ⟨μ.a_interior.1.le, μ.a_interior.2.le⟩
    ⟨μ.b_interior.1.le, μ.b_interior.2.le⟩
    μ.e_pos μ.f_pos μ.e_le_cap μ.f_le_cap (by linarith : μ.meanEntropy < μ.b - μ.a)
  exact (c.value_logarithmic_gain hd).trans (c.value_le_cost μ)

end GeneralCK.PsiEndpointPlane

#print axioms GeneralCK.PsiEndpointPlane.law_endpoint_logarithmic_lower
