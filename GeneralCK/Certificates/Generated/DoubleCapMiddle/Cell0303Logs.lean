import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0303
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (223221673 / 1000000000) ≤ -Real.log (10240 / 12801) ∧
    -Real.log (10240 / 12801) ≤ (111610837 / 500000000) := by
  have h := checkLog_sound (w := (2561 / 23041)) (n := 12)
    (lo := (223221673 / 1000000000)) (hi := (111610837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12801 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12801 / 10240) = 1/(10240 / 12801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (223221673 / 1000000000) (111610837 / 500000000) (Real.log (12801 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12801 / 10240) = -Real.log (10240 / 12801) := by
    rw [show ((12801 / 10240) : ℝ) = ((10240 / 12801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (287812289 / 1000000000) ≤ -Real.log (7679 / 10240) ∧
    -Real.log (7679 / 10240) ≤ (28781229 / 100000000) := by
  have h := checkLog_sound (w := (2561 / 17919)) (n := 12)
    (lo := (287812289 / 1000000000)) (hi := (28781229 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7679) = 1/(7679 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-28781229 / 100000000) (-287812289 / 1000000000) (Real.log (7679 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (222987289 / 1000000000) ≤ -Real.log (5120 / 6399) ∧
    -Real.log (5120 / 6399) ≤ (22298729 / 100000000) := by
  have h := checkLog_sound (w := (1279 / 11519)) (n := 12)
    (lo := (222987289 / 1000000000)) (hi := (22298729 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6399 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6399 / 5120) = 1/(5120 / 6399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (222987289 / 1000000000) (22298729 / 100000000) (Real.log (6399 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6399 / 5120) = -Real.log (5120 / 6399) := by
    rw [show ((6399 / 5120) : ℝ) = ((5120 / 6399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (287421689 / 1000000000) ≤ -Real.log (3841 / 5120) ∧
    -Real.log (3841 / 5120) ≤ (28742169 / 100000000) := by
  have h := checkLog_sound (w := (1279 / 8961)) (n := 12)
    (lo := (287421689 / 1000000000)) (hi := (28742169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3841) = 1/(3841 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-28742169 / 100000000) (-287421689 / 1000000000) (Real.log (3841 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (405595307 / 1000000000) ≤ -Real.log (5120 / 7681) ∧
    -Real.log (5120 / 7681) ≤ (101398827 / 250000000) := by
  have h := checkLog_sound (w := (2561 / 12801)) (n := 12)
    (lo := (405595307 / 1000000000)) (hi := (101398827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7681 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7681 / 5120) = 1/(5120 / 7681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (405595307 / 1000000000) (101398827 / 250000000) (Real.log (7681 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7681 / 5120) = -Real.log (5120 / 7681) := by
    rw [show ((7681 / 5120) : ℝ) = ((5120 / 7681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (693537881 / 1000000000) ≤ -Real.log (2559 / 5120) ∧
    -Real.log (2559 / 5120) ≤ (693537883 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 5119)) (n := 12)
    (lo := (390701 / 1000000000)) (hi := (195351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2559) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2559) = 1/(2559 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-693537883 / 1000000000) (-693537881 / 1000000000) (Real.log (2559 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (405204657 / 1000000000) ≤ -Real.log (2560 / 3839) ∧
    -Real.log (2560 / 3839) ≤ (202602329 / 500000000) := by
  have h := checkLog_sound (w := (1279 / 6399)) (n := 12)
    (lo := (405204657 / 1000000000)) (hi := (202602329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3839 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3839 / 2560) = 1/(2560 / 3839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (405204657 / 1000000000) (202602329 / 500000000) (Real.log (3839 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3839 / 2560) = -Real.log (2560 / 3839) := by
    rw [show ((3839 / 2560) : ℝ) = ((2560 / 3839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (138473247 / 200000000) ≤ -Real.log (1281 / 2560) ∧
    -Real.log (1281 / 2560) ≤ (173091559 / 250000000) := by
  have h := checkLog_sound (w := (1279 / 3841)) (n := 12)
    (lo := (138473247 / 200000000)) (hi := (173091559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1281) = 1/(1281 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-173091559 / 250000000) (-138473247 / 200000000) (Real.log (1281 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (305565211 / 1000000000) ≤ -Real.log (62500 / 84837) ∧
    -Real.log (62500 / 84837) ≤ (76391303 / 250000000) := by
  have h := checkLog_sound (w := (22337 / 147337)) (n := 12)
    (lo := (305565211 / 1000000000)) (hi := (76391303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84837 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84837 / 62500) = 1/(62500 / 84837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (305565211 / 1000000000) (76391303 / 250000000) (Real.log (84837 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (84837 / 62500) = -Real.log (62500 / 84837) := by
    rw [show ((84837 / 62500) : ℝ) = ((62500 / 84837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (221110191 / 500000000) ≤ -Real.log (40163 / 62500) ∧
    -Real.log (40163 / 62500) ≤ (442220383 / 1000000000) := by
  have h := checkLog_sound (w := (22337 / 102663)) (n := 12)
    (lo := (221110191 / 500000000)) (hi := (442220383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 40163) = 1/(40163 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-442220383 / 1000000000) (-221110191 / 500000000) (Real.log (40163 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (305882681 / 1000000000) ≤ -Real.log (1000000 / 1357823) ∧
    -Real.log (1000000 / 1357823) ≤ (152941341 / 500000000) := by
  have h := checkLog_sound (w := (357823 / 2357823)) (n := 12)
    (lo := (305882681 / 1000000000)) (hi := (152941341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1357823 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1357823 / 1000000) = 1/(1000000 / 1357823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (305882681 / 1000000000) (152941341 / 500000000) (Real.log (1357823 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1357823 / 1000000) = -Real.log (1000000 / 1357823) := by
    rw [show ((1357823 / 1000000) : ℝ) = ((1000000 / 1357823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (27680707 / 62500000) ≤ -Real.log (642177 / 1000000) ∧
    -Real.log (642177 / 1000000) ≤ (442891313 / 1000000000) := by
  have h := checkLog_sound (w := (357823 / 1642177)) (n := 12)
    (lo := (27680707 / 62500000)) (hi := (442891313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 642177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 642177) = 1/(642177 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-442891313 / 1000000000) (-27680707 / 62500000) (Real.log (642177 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (7271087 / 31250000) ≤ -Real.log (1000000 / 1261971) ∧
    -Real.log (1000000 / 1261971) ≤ (46534957 / 200000000) := by
  have h := checkLog_sound (w := (261971 / 2261971)) (n := 12)
    (lo := (7271087 / 31250000)) (hi := (46534957 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1261971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1261971 / 1000000) = 1/(1000000 / 1261971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (7271087 / 31250000) (46534957 / 200000000) (Real.log (1261971 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1261971 / 1000000) = -Real.log (1000000 / 1261971) := by
    rw [show ((1261971 / 1000000) : ℝ) = ((1000000 / 1261971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (303772159 / 1000000000) ≤ -Real.log (738029 / 1000000) ∧
    -Real.log (738029 / 1000000) ≤ (118661 / 390625) := by
  have h := checkLog_sound (w := (261971 / 1738029)) (n := 12)
    (lo := (303772159 / 1000000000)) (hi := (118661 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 738029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 738029) = 1/(738029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-118661 / 390625) (-303772159 / 1000000000) (Real.log (738029 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (232944167 / 1000000000) ≤ -Real.log (1000000 / 1262311) ∧
    -Real.log (1000000 / 1262311) ≤ (29118021 / 125000000) := by
  have h := checkLog_sound (w := (262311 / 2262311)) (n := 12)
    (lo := (232944167 / 1000000000)) (hi := (29118021 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1262311 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1262311 / 1000000) = 1/(1000000 / 1262311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (232944167 / 1000000000) (29118021 / 125000000) (Real.log (1262311 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1262311 / 1000000) = -Real.log (1000000 / 1262311) := by
    rw [show ((1262311 / 1000000) : ℝ) = ((1000000 / 1262311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (38029119 / 125000000) ≤ -Real.log (737689 / 1000000) ∧
    -Real.log (737689 / 1000000) ≤ (304232953 / 1000000000) := by
  have h := checkLog_sound (w := (262311 / 1737689)) (n := 12)
    (lo := (38029119 / 125000000)) (hi := (304232953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 737689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 737689) = 1/(737689 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-304232953 / 1000000000) (-38029119 / 125000000) (Real.log (737689 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (373892797 / 500000000) ≤ -Real.log (500000000000 / 1056158653487) ∧
    -Real.log (500000000000 / 1056158653487) ≤ (186946399 / 250000000) := by
  have h := checkLog_sound (w := (56158653487 / 2056158653487)) (n := 12)
    (lo := (27319207 / 500000000)) (hi := (10927683 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056158653487 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1056158653487 / 1000000000000) = 1/(500000000000 / 1056158653487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (373892797 / 500000000) (186946399 / 250000000) (Real.log (1056158653487 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1056158653487 / 500000000000) = -Real.log (500000000000 / 1056158653487) := by
    rw [show ((1056158653487 / 500000000000) : ℝ) = ((500000000000 / 1056158653487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (748773993 / 1000000000) ≤ -Real.log (500000000000 / 1057203076411) ∧
    -Real.log (500000000000 / 1057203076411) ≤ (149754799 / 200000000) := by
  have h := checkLog_sound (w := (57203076411 / 2057203076411)) (n := 12)
    (lo := (55626813 / 1000000000)) (hi := (27813407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1057203076411 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1057203076411 / 1000000000000) = 1/(500000000000 / 1057203076411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (748773993 / 1000000000) (149754799 / 200000000) (Real.log (1057203076411 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1057203076411 / 500000000000) = -Real.log (500000000000 / 1057203076411) := by
    rw [show ((1057203076411 / 500000000000) : ℝ) = ((500000000000 / 1057203076411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16763967 / 31250000) ≤ -Real.log (500000000000 / 854960306437) ∧
    -Real.log (500000000000 / 854960306437) ≤ (107289389 / 200000000) := by
  have h := checkLog_sound (w := (354960306437 / 1354960306437)) (n := 12)
    (lo := (16763967 / 31250000)) (hi := (107289389 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((854960306437 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(854960306437 / 500000000000) = 1/(500000000000 / 854960306437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (16763967 / 31250000) (107289389 / 200000000) (Real.log (854960306437 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (854960306437 / 500000000000) = -Real.log (500000000000 / 854960306437) := by
    rw [show ((854960306437 / 500000000000) : ℝ) = ((500000000000 / 854960306437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3357357 / 6250000) ≤ -Real.log (31250000000 / 53474050379) ∧
    -Real.log (31250000000 / 53474050379) ≤ (537177121 / 1000000000) := by
  have h := checkLog_sound (w := (22224050379 / 84724050379)) (n := 12)
    (lo := (3357357 / 6250000)) (hi := (537177121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53474050379 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53474050379 / 31250000000) = 1/(31250000000 / 53474050379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3357357 / 6250000) (537177121 / 1000000000) (Real.log (53474050379 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (53474050379 / 31250000000) = -Real.log (31250000000 / 53474050379) := by
    rw [show ((53474050379 / 31250000000) : ℝ) = ((31250000000 / 53474050379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0303
