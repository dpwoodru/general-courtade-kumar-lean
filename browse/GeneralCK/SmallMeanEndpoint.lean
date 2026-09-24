import GeneralCK.SmallMeanEstimates
import GeneralCK.PhysicalSlope
import GeneralCK.Certificates.SmallMeanCertificate

namespace GeneralCK.SmallMean

theorem slope_small_mean {m : ℝ} (hm : 0 < m) (hm' : m ≤ 1/32) :
    deriv Scalar.P (H m) ≤ 4+(23/10)*H m := by
  have hm1 : m < 1 := by linarith
  have hh0 : 0 < H m := H_pos hm hm1
  have ha0 : 0 < H (1/32) := H_pos (by norm_num) (by norm_num)
  have ha1 : H (1/32) < 1 := by
    have h := H_strictMonoOn (a := (1/32 : ℝ)) (b := 1/2)
      ⟨by norm_num,by norm_num⟩ ⟨by norm_num,le_rfl⟩ (by norm_num)
    simpa only [H_half] using h
  have hha : H m ≤ H (1/32) := H_strictMonoOn.monotoneOn
    ⟨hm.le,by linarith⟩ ⟨by norm_num,by norm_num⟩ hm'
  exact Scalar.deriv_P_le_linear_of_secant ha0 ha1 hh0 hha
    Certificates.SmallMean.fixed_secant_lt.le

/-- The two numerical cases needed at the far endpoint of the entropy interval. -/
theorem endpoint_coefficient_nonneg {r t : ℝ} (hr : 0 < r) (hr' : r ≤ 1)
    (ht : 0 ≤ t) (ht' : t ≤ 201/1000) :
    0 ≤ ((1862/2883)-(1/31)*gamma r)*r^2 + (gamma r-23/10)*t := by
  have hg := gamma_pos hr hr'
  have hgu : gamma r < 14/5 := by
    have h := gamma_le_four_log hr hr'
    have hl := Certificates.SmallMean.fixed_log_two_lt
    linarith
  by_cases hc : (23/10 : ℝ) ≤ gamma r
  · have h₁ : 0 ≤ ((1862/2883)-(1/31)*gamma r)*r^2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    exact add_nonneg h₁ (mul_nonneg (sub_nonneg.mpr hc) ht)
  · have hc' : gamma r < 23/10 := lt_of_not_ge hc
    have hr6 : 1/6 ≤ r := by
      by_contra hn
      have hm := gamma_antitone ⟨hr,hr'⟩
        (show (1/6 : ℝ) ∈ Set.Ioc 0 1 by norm_num) (le_of_not_ge hn)
      have hf := Certificates.SmallMean.fixed_gamma_sixth
      linarith
    have hcert := Certificates.SmallMean.small_mean_scalar r hr6 hr'
    have ht := mul_le_mul_of_nonpos_left ht' (show gamma r-23/10 ≤ 0 by linarith)
    nlinarith only [hcert,ht]

/-- Algebraic completion of the endpoint argument; the premises are later
supplied by proved mean estimates and the slope bound. -/
theorem endpoint_nonneg_of_estimates {r t D j α : ℝ}
    (hr : 0 < r) (hr' : r ≤ 1) (ht : 0 ≤ t) (ht' : t ≤ 201/1000)
    (hD : 0 ≤ D) (hDt : D ≤ t) (hDr : D ≤ r^2/31)
    (hj : (4+(1862/2883)*r^2)*D ≤ j) (ha : gamma r*D ≤ α)
    (hP : Scalar.P t-Scalar.P (t-D) ≤ (4+(23/10)*t)*D) :
    0 ≤ j+α*(t-D)-Scalar.P t+Scalar.P (t-D) := by
  have hg := gamma_pos hr hr'
  have hα := mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hDt)
  have hδ := mul_le_mul_of_nonneg_left hDr (mul_nonneg hg.le hD)
  have hq := mul_nonneg hD (endpoint_coefficient_nonneg hr hr' ht ht')
  nlinarith only [hj,hα,hδ,hP,hq]

end GeneralCK.SmallMean
