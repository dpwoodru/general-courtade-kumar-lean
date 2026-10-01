import GeneralCK.Certificates.SmallMeanCoverage
import GeneralCK.Certificates.SmallMeanFixed
import GeneralCK.SmallMeanAnalytic

namespace GeneralCK.Certificates.SmallMean

/-- All twenty original closed intervals, with the analytic monotonicity discharged. -/
theorem small_mean_scalar (r : ℝ) (hl : (1/6 : ℝ) ≤ r) (hu : r ≤ 1) :
    0 < (1862/2883)*r^2-(23/10)*(201/1000)+
      GeneralCK.SmallMean.gamma r*((201/1000)-(1/31)*r^2) :=
  scalar_certificate GeneralCK.SmallMean.gamma GeneralCK.SmallMean.gamma_antitone rfl r hl hu

theorem fixed_gamma_sixth : (23/10 : ℝ) < GeneralCK.SmallMean.gamma (1/6) := gamma_sixth_gt

theorem fixed_log_two_lt : Real.log 2 < (7/10 : ℝ) := by
  have h := PilotData.log_two.2
  norm_num only [div_one] at h
  linarith only [h]

theorem fixed_small_ratio_positive : (0 : ℝ) < 1862/2883-(14/5)*(1/31) := by norm_num

end GeneralCK.Certificates.SmallMean
