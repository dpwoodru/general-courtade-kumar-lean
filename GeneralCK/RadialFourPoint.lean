import GeneralCK.RadialConcavity
import GeneralCK.BellmanAssembly

namespace GeneralCK
open Set

theorem F_sqrt_add_le {h x y : ℝ} (hh : 0 < h) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    F (Real.sqrt (x+y)) h ≤ F (Real.sqrt x) h + F (Real.sqrt y) h := by
  by_cases hs : x+y = 0
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    subst x; subst y
    simp [F]
  have hs0 : 0 < x+y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hs)
  have hw : y/(x+y)+x/(x+y) = 1 := by field_simp; ring
  have h₁ := (concaveOn_F_sqrt hh).2 (show (0:ℝ) ∈ Ici 0 by simp)
    (show x+y ∈ Ici 0 from hs0.le) (div_nonneg hy hs0.le) (div_nonneg hx hs0.le) hw
  have h₂ := (concaveOn_F_sqrt hh).2 (show (0:ℝ) ∈ Ici 0 by simp)
    (show x+y ∈ Ici 0 from hs0.le) (div_nonneg hx hs0.le) (div_nonneg hy hs0.le)
    (by linarith : x/(x+y)+y/(x+y)=1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sqrt_zero,
    show F 0 h = 0 by simp [F], div_mul_cancel₀ _ hs] at h₁ h₂
  have he : y/(x+y)*F (Real.sqrt (x+y)) h + x/(x+y)*F (Real.sqrt (x+y)) h =
      F (Real.sqrt (x+y)) h := by rw [← add_mul, hw, one_mul]
  linarith

/-- The radial four-point inequality, including radii crossing zero. -/
theorem F_four_point {h : ℝ} (hh : 0 < h) (r d : ℝ) :
    (F |r-d| h + F |r+d| h)/2 ≤ F |r| h + F |d| h := by
  have hs := F_sqrt_add_le hh (sq_nonneg r) (sq_nonneg d)
  simp only [Real.sqrt_sq_eq_abs] at hs
  exact (F_average_le_sqrt hh r d).trans hs

theorem equal_entropy_phi_gap_le_radial {e : ℝ} (he : 0 < e) (a b : ℝ) :
    candidateGap phi a b e e ≤ F |a-b| e := by
  have hf := F_four_point he (1-a-b) (b-a)
  have h₁ : 1-a-b-(b-a) = 1-2*b := by ring
  have h₂ : 1-a-b+(b-a) = 1-2*a := by ring
  have h₃ : 1-2*((a+b)/2) = 1-a-b := by ring
  rw [h₁,h₂,abs_sub_comm b a] at hf
  unfold candidateGap phi
  rw [show (e+e)/2=e by ring,h₃]
  linarith

end GeneralCK
