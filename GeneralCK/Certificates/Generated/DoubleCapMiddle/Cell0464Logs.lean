import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0464
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

theorem reflection_log_1_neg : (184759987 / 1000000000) ≤ -Real.log (5120 / 6159) ∧
    -Real.log (5120 / 6159) ≤ (46189997 / 250000000) := by
  have h := checkLog_sound (w := (1039 / 11279)) (n := 12)
    (lo := (184759987 / 1000000000)) (hi := (46189997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6159 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6159 / 5120) = 1/(5120 / 6159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (184759987 / 1000000000) (46189997 / 250000000) (Real.log (6159 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6159 / 5120) = -Real.log (5120 / 6159) := by
    rw [show ((6159 / 5120) : ℝ) = ((5120 / 6159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (113406191 / 500000000) ≤ -Real.log (4081 / 5120) ∧
    -Real.log (4081 / 5120) ≤ (226812383 / 1000000000) := by
  have h := checkLog_sound (w := (1039 / 9201)) (n := 12)
    (lo := (113406191 / 500000000)) (hi := (226812383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4081) = 1/(4081 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-226812383 / 1000000000) (-113406191 / 500000000) (Real.log (4081 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (184516411 / 1000000000) ≤ -Real.log (2048 / 2463) ∧
    -Real.log (2048 / 2463) ≤ (46129103 / 250000000) := by
  have h := checkLog_sound (w := (415 / 4511)) (n := 12)
    (lo := (184516411 / 1000000000)) (hi := (46129103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2463 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2463 / 2048) = 1/(2048 / 2463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (184516411 / 1000000000) (46129103 / 250000000) (Real.log (2463 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2463 / 2048) = -Real.log (2048 / 2463) := by
    rw [show ((2463 / 2048) : ℝ) = ((2048 / 2463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (226444893 / 1000000000) ≤ -Real.log (1633 / 2048) ∧
    -Real.log (1633 / 2048) ≤ (113222447 / 500000000) := by
  have h := checkLog_sound (w := (415 / 3681)) (n := 12)
    (lo := (226444893 / 1000000000)) (hi := (113222447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1633) = 1/(1633 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-113222447 / 500000000) (-226444893 / 1000000000) (Real.log (1633 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (34064877 / 100000000) ≤ -Real.log (2560 / 3599) ∧
    -Real.log (2560 / 3599) ≤ (340648771 / 1000000000) := by
  have h := checkLog_sound (w := (1039 / 6159)) (n := 12)
    (lo := (34064877 / 100000000)) (hi := (340648771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3599 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3599 / 2560) = 1/(2560 / 3599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (34064877 / 100000000) (340648771 / 1000000000) (Real.log (3599 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3599 / 2560) = -Real.log (2560 / 3599) := by
    rw [show ((3599 / 2560) : ℝ) = ((2560 / 3599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (104127849 / 200000000) ≤ -Real.log (1521 / 2560) ∧
    -Real.log (1521 / 2560) ≤ (260319623 / 500000000) := by
  have h := checkLog_sound (w := (1039 / 4081)) (n := 12)
    (lo := (104127849 / 200000000)) (hi := (260319623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1521) = 1/(1521 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-260319623 / 500000000) (-104127849 / 200000000) (Real.log (1521 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (340231901 / 1000000000) ≤ -Real.log (1024 / 1439) ∧
    -Real.log (1024 / 1439) ≤ (170115951 / 500000000) := by
  have h := checkLog_sound (w := (415 / 2463)) (n := 12)
    (lo := (340231901 / 1000000000)) (hi := (170115951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1439 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1439 / 1024) = 1/(1024 / 1439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (340231901 / 1000000000) (170115951 / 500000000) (Real.log (1439 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1439 / 1024) = -Real.log (1024 / 1439) := by
    rw [show ((1439 / 1024) : ℝ) = ((1024 / 1439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (519653537 / 1000000000) ≤ -Real.log (609 / 1024) ∧
    -Real.log (609 / 1024) ≤ (259826769 / 500000000) := by
  have h := checkLog_sound (w := (415 / 1633)) (n := 12)
    (lo := (519653537 / 1000000000)) (hi := (259826769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 609) = 1/(609 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-259826769 / 500000000) (-519653537 / 1000000000) (Real.log (609 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (126808831 / 500000000) ≤ -Real.log (1000000 / 1288679) ∧
    -Real.log (1000000 / 1288679) ≤ (253617663 / 1000000000) := by
  have h := checkLog_sound (w := (288679 / 2288679)) (n := 12)
    (lo := (126808831 / 500000000)) (hi := (253617663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1288679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1288679 / 1000000) = 1/(1000000 / 1288679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (126808831 / 500000000) (253617663 / 1000000000) (Real.log (1288679 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1288679 / 1000000) = -Real.log (1000000 / 1288679) := by
    rw [show ((1288679 / 1000000) : ℝ) = ((1000000 / 1288679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (170315737 / 500000000) ≤ -Real.log (711321 / 1000000) ∧
    -Real.log (711321 / 1000000) ≤ (13625259 / 40000000) := by
  have h := checkLog_sound (w := (288679 / 1711321)) (n := 12)
    (lo := (170315737 / 500000000)) (hi := (13625259 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 711321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 711321) = 1/(711321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13625259 / 40000000) (-170315737 / 500000000) (Real.log (711321 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (253947403 / 1000000000) ≤ -Real.log (62500 / 80569) ∧
    -Real.log (62500 / 80569) ≤ (63486851 / 250000000) := by
  have h := checkLog_sound (w := (18069 / 143069)) (n := 12)
    (lo := (253947403 / 1000000000)) (hi := (63486851 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80569 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80569 / 62500) = 1/(62500 / 80569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (253947403 / 1000000000) (63486851 / 250000000) (Real.log (80569 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (80569 / 62500) = -Real.log (62500 / 80569) := by
    rw [show ((80569 / 62500) : ℝ) = ((62500 / 80569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (85307283 / 250000000) ≤ -Real.log (44431 / 62500) ∧
    -Real.log (44431 / 62500) ≤ (341229133 / 1000000000) := by
  have h := checkLog_sound (w := (18069 / 106931)) (n := 12)
    (lo := (85307283 / 250000000)) (hi := (341229133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44431) = 1/(44431 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-341229133 / 1000000000) (-85307283 / 250000000) (Real.log (44431 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (189750559 / 1000000000) ≤ -Real.log (250000 / 302237) ∧
    -Real.log (250000 / 302237) ≤ (1185941 / 6250000) := by
  have h := checkLog_sound (w := (52237 / 552237)) (n := 12)
    (lo := (189750559 / 1000000000)) (hi := (1185941 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302237 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302237 / 250000) = 1/(250000 / 302237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (189750559 / 1000000000) (1185941 / 6250000) (Real.log (302237 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (302237 / 250000) = -Real.log (250000 / 302237) := by
    rw [show ((302237 / 250000) : ℝ) = ((250000 / 302237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (234391573 / 1000000000) ≤ -Real.log (197763 / 250000) ∧
    -Real.log (197763 / 250000) ≤ (117195787 / 500000000) := by
  have h := checkLog_sound (w := (52237 / 447763)) (n := 12)
    (lo := (234391573 / 1000000000)) (hi := (117195787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 197763) = 1/(197763 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-117195787 / 500000000) (-234391573 / 1000000000) (Real.log (197763 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (95008849 / 500000000) ≤ -Real.log (1000000 / 1209271) ∧
    -Real.log (1000000 / 1209271) ≤ (190017699 / 1000000000) := by
  have h := checkLog_sound (w := (209271 / 2209271)) (n := 12)
    (lo := (95008849 / 500000000)) (hi := (190017699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1209271 / 1000000) = 1/(1000000 / 1209271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (95008849 / 500000000) (190017699 / 1000000000) (Real.log (1209271 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1209271 / 1000000) = -Real.log (1000000 / 1209271) := by
    rw [show ((1209271 / 1000000) : ℝ) = ((1000000 / 1209271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (117399987 / 500000000) ≤ -Real.log (790729 / 1000000) ∧
    -Real.log (790729 / 1000000) ≤ (9391999 / 40000000) := by
  have h := checkLog_sound (w := (209271 / 1790729)) (n := 12)
    (lo := (117399987 / 500000000)) (hi := (9391999 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 790729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 790729) = 1/(790729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-9391999 / 40000000) (-117399987 / 500000000) (Real.log (790729 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (37140571 / 62500000) ≤ -Real.log (100000000000 / 181167011799) ∧
    -Real.log (100000000000 / 181167011799) ≤ (594249137 / 1000000000) := by
  have h := checkLog_sound (w := (81167011799 / 281167011799)) (n := 12)
    (lo := (37140571 / 62500000)) (hi := (594249137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181167011799 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181167011799 / 100000000000) = 1/(100000000000 / 181167011799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (37140571 / 62500000) (594249137 / 1000000000) (Real.log (181167011799 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (181167011799 / 100000000000) = -Real.log (100000000000 / 181167011799) := by
    rw [show ((181167011799 / 100000000000) : ℝ) = ((100000000000 / 181167011799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (74397067 / 125000000) ≤ -Real.log (100000000000 / 181335103869) ∧
    -Real.log (100000000000 / 181335103869) ≤ (595176537 / 1000000000) := by
  have h := checkLog_sound (w := (81335103869 / 281335103869)) (n := 12)
    (lo := (74397067 / 125000000)) (hi := (595176537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181335103869 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181335103869 / 100000000000) = 1/(100000000000 / 181335103869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (74397067 / 125000000) (595176537 / 1000000000) (Real.log (181335103869 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (181335103869 / 100000000000) = -Real.log (100000000000 / 181335103869) := by
    rw [show ((181335103869 / 100000000000) : ℝ) = ((100000000000 / 181335103869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (424142133 / 1000000000) ≤ -Real.log (500000000000 / 764139399179) ∧
    -Real.log (500000000000 / 764139399179) ≤ (212071067 / 500000000) := by
  have h := checkLog_sound (w := (264139399179 / 1264139399179)) (n := 12)
    (lo := (424142133 / 1000000000)) (hi := (212071067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764139399179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764139399179 / 500000000000) = 1/(500000000000 / 764139399179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (424142133 / 1000000000) (212071067 / 500000000) (Real.log (764139399179 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (764139399179 / 500000000000) = -Real.log (500000000000 / 764139399179) := by
    rw [show ((764139399179 / 500000000000) : ℝ) = ((500000000000 / 764139399179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (53102209 / 125000000) ≤ -Real.log (500000000000 / 764655779667) ∧
    -Real.log (500000000000 / 764655779667) ≤ (424817673 / 1000000000) := by
  have h := checkLog_sound (w := (264655779667 / 1264655779667)) (n := 12)
    (lo := (53102209 / 125000000)) (hi := (424817673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764655779667 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764655779667 / 500000000000) = 1/(500000000000 / 764655779667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (53102209 / 125000000) (424817673 / 1000000000) (Real.log (764655779667 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (764655779667 / 500000000000) = -Real.log (500000000000 / 764655779667) := by
    rw [show ((764655779667 / 500000000000) : ℝ) = ((500000000000 / 764655779667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0464
