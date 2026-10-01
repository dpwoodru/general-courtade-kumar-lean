import GeneralCK.PhiEntropyConvexity
import GeneralCK.BellmanAssembly
import GeneralCK.LogSum

namespace GeneralCK
open Set

theorem psi_entropy_convexOn {m : ℝ} : ConvexOn ℝ (Ioc 0 (H m)) (psi m) := by
  refine ⟨convex_Ioc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hcap := H_le_one m
  have h := Scalar.eta_convexOn_Ioc.2
    (show x+1-H m ∈ Ioc 0 1 by constructor <;> linarith [hx.1,hx.2])
    (show y+1-H m ∈ Ioc 0 1 by constructor <;> linarith [hy.1,hy.2]) ha hb hab
  simp only [smul_eq_mul,psi] at h ⊢
  convert! h using 1
  congr 1
  nlinarith

/-- Taking the maximum preserves entropy convexity of both candidates. -/
theorem B_entropy_convexOn {m : ℝ} (hm : 0 < m) (hm' : m < 1) :
    ConvexOn ℝ (Ioc 0 (H m)) (B m) :=
  (phi_entropy_convexOn hm hm').sup psi_entropy_convexOn

namespace InteriorLaw
variable {ι : Type*} [Fintype ι]

/-- At equal means the complete hybrid gap is nonpositive, for arbitrary entropy splits. -/
theorem equal_mean_gap_nonpos (μ : InteriorLaw ι) (heq : μ.a = μ.b) : μ.gap ≤ 0 := by
  have hj := (B_entropy_convexOn μ.a_interior.1 μ.a_interior.2).2
    (show μ.e ∈ Ioc 0 (H μ.a) from ⟨μ.e_pos,μ.e_le_cap⟩)
    (show μ.f ∈ Ioc 0 (H μ.a) from ⟨μ.f_pos,by rw [heq]; exact μ.f_le_cap⟩)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hj
  unfold gap
  rw [← heq,show (μ.a+μ.a)/2=μ.a by ring]
  have hmid : (1/2:ℝ)*μ.e+(1/2)*μ.f=(μ.e+μ.f)/2 := by ring
  rw [hmid] at hj
  linarith

theorem equal_mean_phi_gap_nonpos (μ : InteriorLaw ι) (heq : μ.a = μ.b) :
    candidateGap phi μ.a μ.b μ.e μ.f ≤ 0 := by
  have hj := (phi_entropy_convexOn μ.a_interior.1 μ.a_interior.2).2
    (show μ.e ∈ Ioc 0 (H μ.a) from ⟨μ.e_pos,μ.e_le_cap⟩)
    (show μ.f ∈ Ioc 0 (H μ.a) from ⟨μ.f_pos,by rw [heq]; exact μ.f_le_cap⟩)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hj
  unfold candidateGap
  rw [← heq,show (μ.a+μ.a)/2=μ.a by ring]
  have hmid : (1/2:ℝ)*μ.e+(1/2)*μ.f=(μ.e+μ.f)/2 := by ring
  rw [hmid] at hj
  linarith

/-- The equal-mean case of the full hybrid Bellman inequality has no active-branch premise. -/
theorem equal_mean_hybrid (μ : InteriorLaw ι) (heq : μ.a = μ.b) : μ.gap ≤ μ.cost := by
  have hc : 0 ≤ μ.cost := by simpa [← heq,interiorCost] using LogSum.cost_lower_bound μ
  exact (μ.equal_mean_gap_nonpos heq).trans hc

end InteriorLaw
end GeneralCK
