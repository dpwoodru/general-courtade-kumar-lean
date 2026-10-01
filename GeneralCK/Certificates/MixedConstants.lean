import GeneralCK.Certificates.MixedBounds

namespace GeneralCK.Certificates.Mixed

theorem log_inv_twenty_one : (608904487 / 200000000) ≤ -Real.log (1 / 21) ∧
    -Real.log (1 / 21) ≤ (76113061 / 25000000) := by
  have h := checkLog_sound (w := (5 / 37)) (n := 12)
    (lo := (54386743 / 200000000)) (hi := (67983429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21 / 16) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(21 / 16) = 1/(1 / 21) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_twenty_one_gt_three : (3 : ℝ) < Real.log 21 := by
  have h := log_inv_twenty_one
  rw [one_div, Real.log_inv, neg_neg] at h
  linarith only [h.1]

theorem log_two_gt_69 : (69/100 : ℝ) < Real.log 2 := by
  have h := PilotData.log_two
  norm_num at h
  linarith only [h.1]

end GeneralCK.Certificates.Mixed
