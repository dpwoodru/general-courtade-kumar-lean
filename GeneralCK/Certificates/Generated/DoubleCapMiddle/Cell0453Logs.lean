import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0453
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

theorem reflection_log_1_neg : (187435411 / 1000000000) ≤ -Real.log (10240 / 12351) ∧
    -Real.log (10240 / 12351) ≤ (46858853 / 250000000) := by
  have h := checkLog_sound (w := (2111 / 22591)) (n := 12)
    (lo := (187435411 / 1000000000)) (hi := (46858853 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12351 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12351 / 10240) = 1/(10240 / 12351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (187435411 / 1000000000) (46858853 / 250000000) (Real.log (12351 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12351 / 10240) = -Real.log (10240 / 12351) := by
    rw [show ((12351 / 10240) : ℝ) = ((10240 / 12351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (28857963 / 125000000) ≤ -Real.log (8129 / 10240) ∧
    -Real.log (8129 / 10240) ≤ (46172741 / 200000000) := by
  have h := checkLog_sound (w := (2111 / 18369)) (n := 12)
    (lo := (28857963 / 125000000)) (hi := (46172741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8129) = 1/(8129 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-46172741 / 200000000) (-28857963 / 125000000) (Real.log (8129 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (187192487 / 1000000000) ≤ -Real.log (2560 / 3087) ∧
    -Real.log (2560 / 3087) ≤ (23399061 / 125000000) := by
  have h := checkLog_sound (w := (527 / 5647)) (n := 12)
    (lo := (187192487 / 1000000000)) (hi := (23399061 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3087 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3087 / 2560) = 1/(2560 / 3087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (187192487 / 1000000000) (23399061 / 125000000) (Real.log (3087 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3087 / 2560) = -Real.log (2560 / 3087) := by
    rw [show ((3087 / 2560) : ℝ) = ((2560 / 3087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (230494723 / 1000000000) ≤ -Real.log (2033 / 2560) ∧
    -Real.log (2033 / 2560) ≤ (57623681 / 250000000) := by
  have h := checkLog_sound (w := (527 / 4593)) (n := 12)
    (lo := (230494723 / 1000000000)) (hi := (57623681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2033) = 1/(2033 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-57623681 / 250000000) (-230494723 / 1000000000) (Real.log (2033 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (3452229 / 10000000) ≤ -Real.log (5120 / 7231) ∧
    -Real.log (5120 / 7231) ≤ (345222901 / 1000000000) := by
  have h := checkLog_sound (w := (2111 / 12351)) (n := 12)
    (lo := (3452229 / 10000000)) (hi := (345222901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7231 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7231 / 5120) = 1/(5120 / 7231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (3452229 / 10000000) (345222901 / 1000000000) (Real.log (7231 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7231 / 5120) = -Real.log (5120 / 7231) := by
    rw [show ((7231 / 5120) : ℝ) = ((5120 / 7231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (531546641 / 1000000000) ≤ -Real.log (3009 / 5120) ∧
    -Real.log (3009 / 5120) ≤ (265773321 / 500000000) := by
  have h := checkLog_sound (w := (2111 / 8129)) (n := 12)
    (lo := (531546641 / 1000000000)) (hi := (265773321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3009) = 1/(3009 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-265773321 / 500000000) (-531546641 / 1000000000) (Real.log (3009 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (344807933 / 1000000000) ≤ -Real.log (1280 / 1807) ∧
    -Real.log (1280 / 1807) ≤ (172403967 / 500000000) := by
  have h := checkLog_sound (w := (527 / 3087)) (n := 12)
    (lo := (344807933 / 1000000000)) (hi := (172403967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1807 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1807 / 1280) = 1/(1280 / 1807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (344807933 / 1000000000) (172403967 / 500000000) (Real.log (1807 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1807 / 1280) = -Real.log (1280 / 1807) := by
    rw [show ((1807 / 1280) : ℝ) = ((1280 / 1807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (530550129 / 1000000000) ≤ -Real.log (753 / 1280) ∧
    -Real.log (753 / 1280) ≤ (53055013 / 100000000) := by
  have h := checkLog_sound (w := (527 / 2033)) (n := 12)
    (lo := (530550129 / 1000000000)) (hi := (53055013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 753) = 1/(753 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-53055013 / 100000000) (-530550129 / 1000000000) (Real.log (753 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (32153889 / 125000000) ≤ -Real.log (31250 / 40417) ∧
    -Real.log (31250 / 40417) ≤ (257231113 / 1000000000) := by
  have h := checkLog_sound (w := (9167 / 71667)) (n := 12)
    (lo := (32153889 / 125000000)) (hi := (257231113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40417 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40417 / 31250) = 1/(31250 / 40417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (32153889 / 125000000) (257231113 / 1000000000) (Real.log (40417 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (40417 / 31250) = -Real.log (31250 / 40417) := by
    rw [show ((40417 / 31250) : ℝ) = ((31250 / 40417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (173605647 / 500000000) ≤ -Real.log (22083 / 31250) ∧
    -Real.log (22083 / 31250) ≤ (69442259 / 200000000) := by
  have h := checkLog_sound (w := (9167 / 53333)) (n := 12)
    (lo := (173605647 / 500000000)) (hi := (69442259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 22083) = 1/(22083 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-69442259 / 200000000) (-173605647 / 500000000) (Real.log (22083 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (257559663 / 1000000000) ≤ -Real.log (1000000 / 1293769) ∧
    -Real.log (1000000 / 1293769) ≤ (16097479 / 62500000) := by
  have h := checkLog_sound (w := (293769 / 2293769)) (n := 12)
    (lo := (257559663 / 1000000000)) (hi := (16097479 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1293769 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1293769 / 1000000) = 1/(1000000 / 1293769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (257559663 / 1000000000) (16097479 / 62500000) (Real.log (1293769 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1293769 / 1000000) = -Real.log (1000000 / 1293769) := by
    rw [show ((1293769 / 1000000) : ℝ) = ((1000000 / 1293769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (347812899 / 1000000000) ≤ -Real.log (706231 / 1000000) ∧
    -Real.log (706231 / 1000000) ≤ (3478129 / 10000000) := by
  have h := checkLog_sound (w := (293769 / 1706231)) (n := 12)
    (lo := (347812899 / 1000000000)) (hi := (3478129 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 706231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 706231) = 1/(706231 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3478129 / 10000000) (-347812899 / 1000000000) (Real.log (706231 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (96337223 / 500000000) ≤ -Real.log (125000 / 151561) ∧
    -Real.log (125000 / 151561) ≤ (192674447 / 1000000000) := by
  have h := checkLog_sound (w := (26561 / 276561)) (n := 12)
    (lo := (96337223 / 500000000)) (hi := (192674447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151561 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151561 / 125000) = 1/(125000 / 151561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (96337223 / 500000000) (192674447 / 1000000000) (Real.log (151561 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (151561 / 125000) = -Real.log (125000 / 151561) := by
    rw [show ((151561 / 125000) : ℝ) = ((125000 / 151561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (23887667 / 100000000) ≤ -Real.log (98439 / 125000) ∧
    -Real.log (98439 / 125000) ≤ (238876671 / 1000000000) := by
  have h := checkLog_sound (w := (26561 / 223439)) (n := 12)
    (lo := (23887667 / 100000000)) (hi := (238876671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 98439) = 1/(98439 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-238876671 / 1000000000) (-23887667 / 100000000) (Real.log (98439 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (19294163 / 100000000) ≤ -Real.log (250000 / 303203) ∧
    -Real.log (250000 / 303203) ≤ (192941631 / 1000000000) := by
  have h := checkLog_sound (w := (53203 / 553203)) (n := 12)
    (lo := (19294163 / 100000000)) (hi := (192941631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303203 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303203 / 250000) = 1/(250000 / 303203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19294163 / 100000000) (192941631 / 1000000000) (Real.log (303203 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (303203 / 250000) = -Real.log (250000 / 303203) := by
    rw [show ((303203 / 250000) : ℝ) = ((250000 / 303203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (239288177 / 1000000000) ≤ -Real.log (196797 / 250000) ∧
    -Real.log (196797 / 250000) ≤ (119644089 / 500000000) := by
  have h := checkLog_sound (w := (53203 / 446797)) (n := 12)
    (lo := (239288177 / 1000000000)) (hi := (119644089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 196797) = 1/(196797 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-119644089 / 500000000) (-239288177 / 1000000000) (Real.log (196797 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (302221203 / 500000000) ≤ -Real.log (500000000000 / 915115699859) ∧
    -Real.log (500000000000 / 915115699859) ≤ (604442407 / 1000000000) := by
  have h := checkLog_sound (w := (415115699859 / 1415115699859)) (n := 12)
    (lo := (302221203 / 500000000)) (hi := (604442407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((915115699859 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(915115699859 / 500000000000) = 1/(500000000000 / 915115699859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (302221203 / 500000000) (604442407 / 1000000000) (Real.log (915115699859 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (915115699859 / 500000000000) = -Real.log (500000000000 / 915115699859) := by
    rw [show ((915115699859 / 500000000000) : ℝ) = ((500000000000 / 915115699859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (605372563 / 1000000000) ≤ -Real.log (25000000000 / 45798364841) ∧
    -Real.log (25000000000 / 45798364841) ≤ (151343141 / 250000000) := by
  have h := checkLog_sound (w := (20798364841 / 70798364841)) (n := 12)
    (lo := (605372563 / 1000000000)) (hi := (151343141 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45798364841 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45798364841 / 25000000000) = 1/(25000000000 / 45798364841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (605372563 / 1000000000) (151343141 / 250000000) (Real.log (45798364841 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (45798364841 / 25000000000) = -Real.log (25000000000 / 45798364841) := by
    rw [show ((45798364841 / 25000000000) : ℝ) = ((25000000000 / 45798364841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (431551117 / 1000000000) ≤ -Real.log (500000000000 / 769821920173) ∧
    -Real.log (500000000000 / 769821920173) ≤ (215775559 / 500000000) := by
  have h := checkLog_sound (w := (269821920173 / 1269821920173)) (n := 12)
    (lo := (431551117 / 1000000000)) (hi := (215775559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769821920173 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(769821920173 / 500000000000) = 1/(500000000000 / 769821920173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (431551117 / 1000000000) (215775559 / 500000000) (Real.log (769821920173 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (769821920173 / 500000000000) = -Real.log (500000000000 / 769821920173) := by
    rw [show ((769821920173 / 500000000000) : ℝ) = ((500000000000 / 769821920173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (432229807 / 1000000000) ≤ -Real.log (500000000000 / 770344568261) ∧
    -Real.log (500000000000 / 770344568261) ≤ (27014363 / 62500000) := by
  have h := checkLog_sound (w := (270344568261 / 1270344568261)) (n := 12)
    (lo := (432229807 / 1000000000)) (hi := (27014363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((770344568261 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(770344568261 / 500000000000) = 1/(500000000000 / 770344568261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (432229807 / 1000000000) (27014363 / 62500000) (Real.log (770344568261 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (770344568261 / 500000000000) = -Real.log (500000000000 / 770344568261) := by
    rw [show ((770344568261 / 500000000000) : ℝ) = ((500000000000 / 770344568261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0453
