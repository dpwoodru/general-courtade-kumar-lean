import GeneralCK.PsiEndpointPlaneGlobal

/-!
# The radial cost floor for every positive mean difference

Reflecting the global supporting plane in the opposite diagonal gives equal
entropy coefficients. Its finite-law consequence depends only on the average
entropy; no lower bound on the distance/entropy ratio is required.
-/

namespace GeneralCK.PsiEndpointPlane

theorem exists_symmetric_supporting_plane {x : ℝ} (hx : 0 < x) (hx' : x < 1 / 2) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      (∀ u v : ℝ, 0 < u → u < 1 → 0 < v → v < 1 →
        C * (v - u) ≤ naturalCost u v + K * Real.binEntropy u + K * Real.binEntropy v) ∧
      C * ((1 - x) - x) = naturalCost x (1 - x) + 2 * K * Real.binEntropy x := by
  obtain ⟨A, B, C, hA, hB, hC, hplane, heq⟩ := exists_supporting_plane
    hx hx' (show 1 / 2 < 1 - x by linarith) (show 1 - x < 1 by linarith)
  refine ⟨(A + B) / 2, C, by positivity, hC, ?_, ?_⟩
  · intro u v hu hu1 hv hv1
    have h := hplane u v hu hu1 hv hv1
    have hr := hplane (1 - v) (1 - u) (by linarith) (by linarith)
      (by linarith) (by linarith)
    have hcost : naturalCost (1 - v) (1 - u) = naturalCost u v := by
      simp only [naturalCost, interiorCost_complement, interiorCost_comm v u]
    rw [hcost, Real.binEntropy_one_sub, Real.binEntropy_one_sub] at hr
    linarith
  · rw [Real.binEntropy_one_sub] at heq
    nlinarith only [heq]

end GeneralCK.PsiEndpointPlane

namespace GeneralCK.PsiEndpointContact.Contact
open PsiEndpointPlane

theorem equal_value_eq_F {d E : ℝ} (c : Contact d E E) : c.value = F d E := by
  have heq := c.equal_coordinate_eq
  have hd := congrArg (fun z : ℝ => z * J c.left) c.difference_eq
  simp only [← heq] at hd
  rw [F, if_neg c.difference_pos.ne', c.equal_radialContact]
  simp only [value, ← heq, interiorCost, J_complement]
  nlinarith only [hd]

/-- Equal-entropy contacts compare against laws with arbitrary individual
entropies whose average matches the contact entropy. -/
theorem equal_value_le_cost {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (c : Contact (μ.b - μ.a) μ.meanEntropy μ.meanEntropy) :
    c.value ≤ μ.cost := by
  obtain ⟨K, C, _, _, hplane, hcontact⟩ :=
    exists_symmetric_supporting_plane c.left_pos c.left_lt_half
  have h := averaged_supporting_plane μ hplane
  have hc := congrArg (fun z : ℝ => c.mass * z) hcontact
  have hd := congrArg (fun z : ℝ => C * z) c.difference_eq
  have he := congrArg (fun z : ℝ => 2 * K * Real.log 2 * z) c.entropy_left_eq
  simp only [naturalCost, binEntropy_eq_log_two_mul_H] at hc
  simp only [← c.equal_coordinate_eq] at hd
  unfold InteriorLaw.meanEntropy at he
  have hval : C * (μ.b - μ.a) = Real.log 2 * c.value +
      K * (Real.log 2 * μ.e) + K * (Real.log 2 * μ.f) := by
    simp only [value, ← c.equal_coordinate_eq]
    nlinarith only [hc, hd, he]
  rw [hval] at h
  nlinarith [log_two_pos]

end GeneralCK.PsiEndpointContact.Contact

namespace GeneralCK.PsiEndpointPlane

/-- Universal radial cost floor: every positive mean difference is allowed,
and the two child entropies may be arbitrarily unequal. -/
theorem law_radial_lower {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a < μ.b) :
    F (μ.b - μ.a) μ.meanEntropy ≤ μ.cost := by
  have hupper : μ.b - μ.a ≤ 1 - entropyInverse μ.e - entropyInverse μ.f := by
    simpa only [PsiEndpointContact.massFunction_one] using
      PsiEndpointContact.feasible_upper_test
        ⟨μ.a_interior.1.le, μ.a_interior.2.le⟩
        ⟨μ.b_interior.1.le, μ.b_interior.2.le⟩
        μ.e_pos.le μ.f_pos.le μ.e_le_cap μ.f_le_cap
  obtain ⟨c⟩ := PsiEndpointContact.exists_equal_entropy_contact μ.e_pos μ.f_pos
    (μ.e_le_cap.trans (H_le_one _)) (μ.f_le_cap.trans (H_le_one _))
    (sub_pos.mpr hab) hupper
  change F (μ.b - μ.a) ((μ.e + μ.f) / 2) ≤ μ.cost
  rw [← c.equal_value_eq_F]
  exact c.equal_value_le_cost μ

end GeneralCK.PsiEndpointPlane

#print axioms GeneralCK.PsiEndpointPlane.exists_symmetric_supporting_plane
#print axioms GeneralCK.PsiEndpointContact.Contact.equal_value_le_cost
#print axioms GeneralCK.PsiEndpointPlane.law_radial_lower
