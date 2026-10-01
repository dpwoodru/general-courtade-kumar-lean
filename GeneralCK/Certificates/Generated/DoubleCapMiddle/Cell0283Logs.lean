import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0283
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

theorem reflection_log_1_neg : (445113 / 1953125) ≤ -Real.log (10240 / 12861) ∧
    -Real.log (10240 / 12861) ≤ (227897857 / 1000000000) := by
  have h := checkLog_sound (w := (2621 / 23101)) (n := 12)
    (lo := (445113 / 1953125)) (hi := (227897857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12861 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12861 / 10240) = 1/(10240 / 12861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (445113 / 1953125) (227897857 / 1000000000) (Real.log (12861 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12861 / 10240) = -Real.log (10240 / 12861) := by
    rw [show ((12861 / 10240) : ℝ) = ((10240 / 12861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (73914123 / 250000000) ≤ -Real.log (7619 / 10240) ∧
    -Real.log (7619 / 10240) ≤ (295656493 / 1000000000) := by
  have h := checkLog_sound (w := (2621 / 17859)) (n := 12)
    (lo := (73914123 / 250000000)) (hi := (295656493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7619) = 1/(7619 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-295656493 / 1000000000) (-73914123 / 250000000) (Real.log (7619 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (113832283 / 500000000) ≤ -Real.log (5120 / 6429) ∧
    -Real.log (5120 / 6429) ≤ (227664567 / 1000000000) := by
  have h := checkLog_sound (w := (1309 / 11549)) (n := 12)
    (lo := (113832283 / 500000000)) (hi := (227664567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6429 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6429 / 5120) = 1/(5120 / 6429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (113832283 / 500000000) (227664567 / 1000000000) (Real.log (6429 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6429 / 5120) = -Real.log (5120 / 6429) := by
    rw [show ((6429 / 5120) : ℝ) = ((5120 / 6429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (295262817 / 1000000000) ≤ -Real.log (3811 / 5120) ∧
    -Real.log (3811 / 5120) ≤ (147631409 / 500000000) := by
  have h := checkLog_sound (w := (1309 / 8931)) (n := 12)
    (lo := (295262817 / 1000000000)) (hi := (147631409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3811) = 1/(3811 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-147631409 / 500000000) (-295262817 / 1000000000) (Real.log (3811 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (413376439 / 1000000000) ≤ -Real.log (5120 / 7741) ∧
    -Real.log (5120 / 7741) ≤ (10334411 / 25000000) := by
  have h := checkLog_sound (w := (2621 / 12861)) (n := 12)
    (lo := (413376439 / 1000000000)) (hi := (10334411 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7741 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7741 / 5120) = 1/(5120 / 7741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (413376439 / 1000000000) (10334411 / 25000000) (Real.log (7741 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7741 / 5120) = -Real.log (5120 / 7741) := by
    rw [show ((7741 / 5120) : ℝ) = ((5120 / 7741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (358631893 / 500000000) ≤ -Real.log (2499 / 5120) ∧
    -Real.log (2499 / 5120) ≤ (179315947 / 250000000) := by
  have h := checkLog_sound (w := (61 / 5059)) (n := 12)
    (lo := (12058303 / 500000000)) (hi := (24116607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2499) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2499) = 1/(2499 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-179315947 / 250000000) (-358631893 / 500000000) (Real.log (2499 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (412988817 / 1000000000) ≤ -Real.log (2560 / 3869) ∧
    -Real.log (2560 / 3869) ≤ (206494409 / 500000000) := by
  have h := checkLog_sound (w := (1309 / 6429)) (n := 12)
    (lo := (412988817 / 1000000000)) (hi := (206494409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3869 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3869 / 2560) = 1/(2560 / 3869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (412988817 / 1000000000) (206494409 / 500000000) (Real.log (3869 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3869 / 2560) = -Real.log (2560 / 3869) := by
    rw [show ((3869 / 2560) : ℝ) = ((2560 / 3869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (358032013 / 500000000) ≤ -Real.log (1251 / 2560) ∧
    -Real.log (1251 / 2560) ≤ (179016007 / 250000000) := by
  have h := checkLog_sound (w := (29 / 2531)) (n := 12)
    (lo := (11458423 / 500000000)) (hi := (22916847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1251) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1251) = 1/(1251 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-179016007 / 250000000) (-358032013 / 500000000) (Real.log (1251 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (311887493 / 1000000000) ≤ -Real.log (1000000 / 1366001) ∧
    -Real.log (1000000 / 1366001) ≤ (155943747 / 500000000) := by
  have h := checkLog_sound (w := (366001 / 2366001)) (n := 12)
    (lo := (311887493 / 1000000000)) (hi := (155943747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1366001 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1366001 / 1000000) = 1/(1000000 / 1366001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (311887493 / 1000000000) (155943747 / 500000000) (Real.log (1366001 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1366001 / 1000000) = -Real.log (1000000 / 1366001) := by
    rw [show ((1366001 / 1000000) : ℝ) = ((1000000 / 1366001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (455707901 / 1000000000) ≤ -Real.log (633999 / 1000000) ∧
    -Real.log (633999 / 1000000) ≤ (227853951 / 500000000) := by
  have h := checkLog_sound (w := (366001 / 1633999)) (n := 12)
    (lo := (455707901 / 1000000000)) (hi := (227853951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 633999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 633999) = 1/(633999 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-227853951 / 500000000) (-455707901 / 1000000000) (Real.log (633999 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (156101847 / 500000000) ≤ -Real.log (1000000 / 1366433) ∧
    -Real.log (1000000 / 1366433) ≤ (62440739 / 200000000) := by
  have h := checkLog_sound (w := (366433 / 2366433)) (n := 12)
    (lo := (156101847 / 500000000)) (hi := (62440739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1366433 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1366433 / 1000000) = 1/(1000000 / 1366433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (156101847 / 500000000) (62440739 / 200000000) (Real.log (1366433 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1366433 / 1000000) = -Real.log (1000000 / 1366433) := by
    rw [show ((1366433 / 1000000) : ℝ) = ((1000000 / 1366433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (456389523 / 1000000000) ≤ -Real.log (633567 / 1000000) ∧
    -Real.log (633567 / 1000000) ≤ (114097381 / 250000000) := by
  have h := checkLog_sound (w := (366433 / 1633567)) (n := 12)
    (lo := (456389523 / 1000000000)) (hi := (114097381 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 633567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 633567) = 1/(633567 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-114097381 / 250000000) (-456389523 / 1000000000) (Real.log (633567 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (238040833 / 1000000000) ≤ -Real.log (1000000 / 1268761) ∧
    -Real.log (1000000 / 1268761) ≤ (119020417 / 500000000) := by
  have h := checkLog_sound (w := (268761 / 2268761)) (n := 12)
    (lo := (238040833 / 1000000000)) (hi := (119020417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1268761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1268761 / 1000000) = 1/(1000000 / 1268761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (238040833 / 1000000000) (119020417 / 500000000) (Real.log (1268761 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1268761 / 1000000) = -Real.log (1000000 / 1268761) := by
    rw [show ((1268761 / 1000000) : ℝ) = ((1000000 / 1268761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (313014923 / 1000000000) ≤ -Real.log (731239 / 1000000) ∧
    -Real.log (731239 / 1000000) ≤ (78253731 / 250000000) := by
  have h := checkLog_sound (w := (268761 / 1731239)) (n := 12)
    (lo := (313014923 / 1000000000)) (hi := (78253731 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 731239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 731239) = 1/(731239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-78253731 / 250000000) (-313014923 / 1000000000) (Real.log (731239 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (238309563 / 1000000000) ≤ -Real.log (500000 / 634551) ∧
    -Real.log (500000 / 634551) ≤ (59577391 / 250000000) := by
  have h := checkLog_sound (w := (134551 / 1134551)) (n := 12)
    (lo := (238309563 / 1000000000)) (hi := (59577391 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((634551 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(634551 / 500000) = 1/(500000 / 634551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (238309563 / 1000000000) (59577391 / 250000000) (Real.log (634551 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (634551 / 500000) = -Real.log (500000 / 634551) := by
    rw [show ((634551 / 500000) : ℝ) = ((500000 / 634551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (313481363 / 1000000000) ≤ -Real.log (365449 / 500000) ∧
    -Real.log (365449 / 500000) ≤ (78370341 / 250000000) := by
  have h := checkLog_sound (w := (134551 / 865449)) (n := 12)
    (lo := (313481363 / 1000000000)) (hi := (78370341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 365449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 365449) = 1/(365449 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-78370341 / 250000000) (-313481363 / 1000000000) (Real.log (365449 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (383797697 / 500000000) ≤ -Real.log (125000000000 / 269322388521) ∧
    -Real.log (125000000000 / 269322388521) ≤ (191898849 / 250000000) := by
  have h := checkLog_sound (w := (19322388521 / 519322388521)) (n := 12)
    (lo := (37224107 / 500000000)) (hi := (14889643 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269322388521 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(269322388521 / 250000000000) = 1/(125000000000 / 269322388521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (383797697 / 500000000) (191898849 / 250000000) (Real.log (269322388521 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (269322388521 / 125000000000) = -Real.log (125000000000 / 269322388521) := by
    rw [show ((269322388521 / 125000000000) : ℝ) = ((125000000000 / 269322388521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (768593217 / 1000000000) ≤ -Real.log (125000000000 / 269591258699) ∧
    -Real.log (125000000000 / 269591258699) ≤ (768593219 / 1000000000) := by
  have h := checkLog_sound (w := (19591258699 / 519591258699)) (n := 12)
    (lo := (75446037 / 1000000000)) (hi := (37723019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269591258699 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(269591258699 / 250000000000) = 1/(125000000000 / 269591258699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (768593217 / 1000000000) (768593219 / 1000000000) (Real.log (269591258699 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (269591258699 / 125000000000) = -Real.log (125000000000 / 269591258699) := by
    rw [show ((269591258699 / 125000000000) : ℝ) = ((125000000000 / 269591258699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (551055757 / 1000000000) ≤ -Real.log (125000000000 / 216885484773) ∧
    -Real.log (125000000000 / 216885484773) ≤ (275527879 / 500000000) := by
  have h := checkLog_sound (w := (91885484773 / 341885484773)) (n := 12)
    (lo := (551055757 / 1000000000)) (hi := (275527879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216885484773 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216885484773 / 125000000000) = 1/(125000000000 / 216885484773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (551055757 / 1000000000) (275527879 / 500000000) (Real.log (216885484773 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (216885484773 / 125000000000) = -Real.log (125000000000 / 216885484773) := by
    rw [show ((216885484773 / 125000000000) : ℝ) = ((125000000000 / 216885484773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (551790927 / 1000000000) ≤ -Real.log (12500000000 / 21704499123) ∧
    -Real.log (12500000000 / 21704499123) ≤ (34486933 / 62500000) := by
  have h := checkLog_sound (w := (9204499123 / 34204499123)) (n := 12)
    (lo := (551790927 / 1000000000)) (hi := (34486933 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21704499123 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21704499123 / 12500000000) = 1/(12500000000 / 21704499123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (551790927 / 1000000000) (34486933 / 62500000) (Real.log (21704499123 / 12500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (21704499123 / 12500000000) = -Real.log (12500000000 / 21704499123) := by
    rw [show ((21704499123 / 12500000000) : ℝ) = ((12500000000 / 21704499123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0283
