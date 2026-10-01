import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell172
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (301116811 / 1000000000) ≤ -Real.log (5120 / 6919) ∧
    -Real.log (5120 / 6919) ≤ (75279203 / 250000000) := by
  have h := checkLog_sound (w := (1799 / 12039)) (n := 12)
    (lo := (301116811 / 1000000000)) (hi := (75279203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6919 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6919 / 5120) = 1/(5120 / 6919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (301116811 / 1000000000) (75279203 / 250000000) (Real.log (6919 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6919 / 5120) = -Real.log (5120 / 6919) := by
    rw [show ((6919 / 5120) : ℝ) = ((5120 / 6919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (27055531 / 62500000) ≤ -Real.log (3321 / 5120) ∧
    -Real.log (3321 / 5120) ≤ (432888497 / 1000000000) := by
  have h := checkLog_sound (w := (1799 / 8441)) (n := 12)
    (lo := (27055531 / 62500000)) (hi := (432888497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3321) = 1/(3321 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-432888497 / 1000000000) (-27055531 / 62500000) (Real.log (3321 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (37585391 / 125000000) ≤ -Real.log (1280 / 1729) ∧
    -Real.log (1280 / 1729) ≤ (300683129 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 3009)) (n := 12)
    (lo := (37585391 / 125000000)) (hi := (300683129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1729 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1729 / 1280) = 1/(1280 / 1729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (37585391 / 125000000) (300683129 / 1000000000) (Real.log (1729 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1729 / 1280) = -Real.log (1280 / 1729) := by
    rw [show ((1729 / 1280) : ℝ) = ((1280 / 1729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (215992781 / 500000000) ≤ -Real.log (831 / 1280) ∧
    -Real.log (831 / 1280) ≤ (431985563 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 2111)) (n := 12)
    (lo := (215992781 / 500000000)) (hi := (431985563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 831) = 1/(831 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-431985563 / 1000000000) (-215992781 / 500000000) (Real.log (831 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (55661857 / 250000000) ≤ -Real.log (50000 / 62469) ∧
    -Real.log (50000 / 62469) ≤ (222647429 / 1000000000) := by
  have h := checkLog_sound (w := (12469 / 112469)) (n := 12)
    (lo := (55661857 / 250000000)) (hi := (222647429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62469 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62469 / 50000) = 1/(50000 / 62469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (55661857 / 250000000) (222647429 / 1000000000) (Real.log (62469 / 50000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (62469 / 50000) = -Real.log (50000 / 62469) := by
    rw [show ((62469 / 50000) : ℝ) = ((50000 / 62469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (286855747 / 1000000000) ≤ -Real.log (37531 / 50000) ∧
    -Real.log (37531 / 50000) ≤ (71713937 / 250000000) := by
  have h := checkLog_sound (w := (12469 / 87531)) (n := 12)
    (lo := (286855747 / 1000000000)) (hi := (71713937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37531) = 1/(37531 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-71713937 / 250000000) (-286855747 / 1000000000) (Real.log (37531 / 50000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (111492969 / 500000000) ≤ -Real.log (1000000 / 1249803) ∧
    -Real.log (1000000 / 1249803) ≤ (222985939 / 1000000000) := by
  have h := checkLog_sound (w := (249803 / 2249803)) (n := 12)
    (lo := (111492969 / 500000000)) (hi := (222985939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249803 / 1000000) = 1/(1000000 / 1249803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (111492969 / 500000000) (222985939 / 1000000000) (Real.log (1249803 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1249803 / 1000000) = -Real.log (1000000 / 1249803) := by
    rw [show ((1249803 / 1000000) : ℝ) = ((1000000 / 1249803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3592743 / 12500000) ≤ -Real.log (750197 / 1000000) ∧
    -Real.log (750197 / 1000000) ≤ (287419441 / 1000000000) := by
  have h := checkLog_sound (w := (249803 / 1750197)) (n := 12)
    (lo := (3592743 / 12500000)) (hi := (287419441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 750197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 750197) = 1/(750197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-287419441 / 1000000000) (-3592743 / 12500000) (Real.log (750197 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16503127 / 100000000) ≤ -Real.log (100000 / 117943) ∧
    -Real.log (100000 / 117943) ≤ (165031271 / 1000000000) := by
  have h := checkLog_sound (w := (17943 / 217943)) (n := 12)
    (lo := (16503127 / 100000000)) (hi := (165031271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117943 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117943 / 100000) = 1/(100000 / 117943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16503127 / 100000000) (165031271 / 1000000000) (Real.log (117943 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (117943 / 100000) = -Real.log (100000 / 117943) := by
    rw [show ((117943 / 100000) : ℝ) = ((100000 / 117943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (98878029 / 500000000) ≤ -Real.log (82057 / 100000) ∧
    -Real.log (82057 / 100000) ≤ (197756059 / 1000000000) := by
  have h := checkLog_sound (w := (17943 / 182057)) (n := 12)
    (lo := (98878029 / 500000000)) (hi := (197756059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 82057) = 1/(82057 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-197756059 / 1000000000) (-98878029 / 500000000) (Real.log (82057 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (165298313 / 1000000000) ≤ -Real.log (200000 / 235949) ∧
    -Real.log (200000 / 235949) ≤ (82649157 / 500000000) := by
  have h := checkLog_sound (w := (35949 / 435949)) (n := 12)
    (lo := (165298313 / 1000000000)) (hi := (82649157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235949 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235949 / 200000) = 1/(200000 / 235949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (165298313 / 1000000000) (82649157 / 500000000) (Real.log (235949 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (235949 / 200000) = -Real.log (200000 / 235949) := by
    rw [show ((235949 / 200000) : ℝ) = ((200000 / 235949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (198140011 / 1000000000) ≤ -Real.log (164051 / 200000) ∧
    -Real.log (164051 / 200000) ≤ (49535003 / 250000000) := by
  have h := checkLog_sound (w := (35949 / 364051)) (n := 12)
    (lo := (198140011 / 1000000000)) (hi := (49535003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 164051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 164051) = 1/(164051 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-49535003 / 250000000) (-198140011 / 1000000000) (Real.log (164051 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (73266869 / 100000000) ≤ -Real.log (125000000000 / 260078219013) ∧
    -Real.log (125000000000 / 260078219013) ≤ (183167173 / 250000000) := by
  have h := checkLog_sound (w := (10078219013 / 510078219013)) (n := 12)
    (lo := (3952151 / 100000000)) (hi := (39521511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((260078219013 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(260078219013 / 250000000000) = 1/(125000000000 / 260078219013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (73266869 / 100000000) (183167173 / 250000000) (Real.log (260078219013 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (260078219013 / 125000000000) = -Real.log (125000000000 / 260078219013) := by
    rw [show ((260078219013 / 125000000000) : ℝ) = ((125000000000 / 260078219013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (734005307 / 1000000000) ≤ -Real.log (125000000000 / 260426076483) ∧
    -Real.log (125000000000 / 260426076483) ≤ (734005309 / 1000000000) := by
  have h := checkLog_sound (w := (10426076483 / 510426076483)) (n := 12)
    (lo := (40858127 / 1000000000)) (hi := (2553633 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((260426076483 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(260426076483 / 250000000000) = 1/(125000000000 / 260426076483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (734005307 / 1000000000) (734005309 / 1000000000) (Real.log (260426076483 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (260426076483 / 125000000000) = -Real.log (125000000000 / 260426076483) := by
    rw [show ((260426076483 / 125000000000) : ℝ) = ((125000000000 / 260426076483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (20380127 / 40000000) ≤ -Real.log (62500000000 / 104029002691) ∧
    -Real.log (62500000000 / 104029002691) ≤ (63687897 / 125000000) := by
  have h := checkLog_sound (w := (41529002691 / 166529002691)) (n := 12)
    (lo := (20380127 / 40000000)) (hi := (63687897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104029002691 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(104029002691 / 62500000000) = 1/(62500000000 / 104029002691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (20380127 / 40000000) (63687897 / 125000000) (Real.log (104029002691 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (104029002691 / 62500000000) = -Real.log (62500000000 / 104029002691) := by
    rw [show ((104029002691 / 62500000000) : ℝ) = ((62500000000 / 104029002691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (510405379 / 1000000000) ≤ -Real.log (500000000000 / 832983203079) ∧
    -Real.log (500000000000 / 832983203079) ≤ (25520269 / 50000000) := by
  have h := checkLog_sound (w := (332983203079 / 1332983203079)) (n := 12)
    (lo := (510405379 / 1000000000)) (hi := (25520269 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((832983203079 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(832983203079 / 500000000000) = 1/(500000000000 / 832983203079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (510405379 / 1000000000) (25520269 / 50000000) (Real.log (832983203079 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (832983203079 / 500000000000) = -Real.log (500000000000 / 832983203079) := by
    rw [show ((832983203079 / 500000000000) : ℝ) = ((500000000000 / 832983203079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (362787329 / 1000000000) ≤ -Real.log (500000000000 / 718665074277) ∧
    -Real.log (500000000000 / 718665074277) ≤ (36278733 / 100000000) := by
  have h := checkLog_sound (w := (218665074277 / 1218665074277)) (n := 12)
    (lo := (362787329 / 1000000000)) (hi := (36278733 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718665074277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718665074277 / 500000000000) = 1/(500000000000 / 718665074277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (362787329 / 1000000000) (36278733 / 100000000) (Real.log (718665074277 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (718665074277 / 500000000000) = -Real.log (500000000000 / 718665074277) := by
    rw [show ((718665074277 / 500000000000) : ℝ) = ((500000000000 / 718665074277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (90859581 / 250000000) ≤ -Real.log (500000000000 / 719133074471) ∧
    -Real.log (500000000000 / 719133074471) ≤ (14537533 / 40000000) := by
  have h := checkLog_sound (w := (219133074471 / 1219133074471)) (n := 12)
    (lo := (90859581 / 250000000)) (hi := (14537533 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719133074471 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719133074471 / 500000000000) = 1/(500000000000 / 719133074471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (90859581 / 250000000) (14537533 / 40000000) (Real.log (719133074471 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (719133074471 / 500000000000) = -Real.log (500000000000 / 719133074471) := by
    rw [show ((719133074471 / 500000000000) : ℝ) = ((500000000000 / 719133074471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16420849 / 500000000) ≤ -Real.log (38707669399 / 40000000000) ∧
    -Real.log (38707669399 / 40000000000) ≤ (32841699 / 1000000000) := by
  have h := checkLog_sound (w := (1292330601 / 78707669399)) (n := 12)
    (lo := (16420849 / 500000000)) (hi := (32841699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38707669399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38707669399) = 1/(38707669399 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-32841699 / 1000000000) (-16420849 / 500000000) (Real.log (38707669399 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (32724787 / 1000000000) ≤ -Real.log (9678048751 / 10000000000) ∧
    -Real.log (9678048751 / 10000000000) ≤ (8181197 / 250000000) := by
  have h := checkLog_sound (w := (321951249 / 19678048751)) (n := 12)
    (lo := (32724787 / 1000000000)) (hi := (8181197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9678048751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9678048751) = 1/(9678048751 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8181197 / 250000000) (-32724787 / 1000000000) (Real.log (9678048751 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell172
