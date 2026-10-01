import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0336
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

theorem reflection_log_1_neg : (215457841 / 1000000000) ≤ -Real.log (5120 / 6351) ∧
    -Real.log (5120 / 6351) ≤ (107728921 / 500000000) := by
  have h := checkLog_sound (w := (1231 / 11471)) (n := 12)
    (lo := (215457841 / 1000000000)) (hi := (107728921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6351 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6351 / 5120) = 1/(5120 / 6351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (215457841 / 1000000000) (107728921 / 500000000) (Real.log (6351 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6351 / 5120) = -Real.log (5120 / 6351) := by
    rw [show ((6351 / 5120) : ℝ) = ((5120 / 6351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (275002383 / 1000000000) ≤ -Real.log (3889 / 5120) ∧
    -Real.log (3889 / 5120) ≤ (17187649 / 62500000) := by
  have h := checkLog_sound (w := (1231 / 9009)) (n := 12)
    (lo := (275002383 / 1000000000)) (hi := (17187649 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3889) = 1/(3889 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-17187649 / 62500000) (-275002383 / 1000000000) (Real.log (3889 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (21522163 / 100000000) ≤ -Real.log (10240 / 12699) ∧
    -Real.log (10240 / 12699) ≤ (215221631 / 1000000000) := by
  have h := checkLog_sound (w := (2459 / 22939)) (n := 12)
    (lo := (21522163 / 100000000)) (hi := (215221631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12699 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12699 / 10240) = 1/(10240 / 12699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (21522163 / 100000000) (215221631 / 1000000000) (Real.log (12699 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12699 / 10240) = -Real.log (10240 / 12699) := by
    rw [show ((12699 / 10240) : ℝ) = ((10240 / 12699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (137308377 / 500000000) ≤ -Real.log (7781 / 10240) ∧
    -Real.log (7781 / 10240) ≤ (54923351 / 200000000) := by
  have h := checkLog_sound (w := (2459 / 18021)) (n := 12)
    (lo := (137308377 / 500000000)) (hi := (54923351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7781) = 1/(7781 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-54923351 / 200000000) (-137308377 / 500000000) (Real.log (7781 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (196311289 / 500000000) ≤ -Real.log (2560 / 3791) ∧
    -Real.log (2560 / 3791) ≤ (392622579 / 1000000000) := by
  have h := checkLog_sound (w := (1231 / 6351)) (n := 12)
    (lo := (196311289 / 500000000)) (hi := (392622579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3791 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3791 / 2560) = 1/(2560 / 3791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (196311289 / 500000000) (392622579 / 1000000000) (Real.log (3791 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3791 / 2560) = -Real.log (2560 / 3791) := by
    rw [show ((3791 / 2560) : ℝ) = ((2560 / 3791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (327790239 / 500000000) ≤ -Real.log (1329 / 2560) ∧
    -Real.log (1329 / 2560) ≤ (655580479 / 1000000000) := by
  have h := checkLog_sound (w := (1231 / 3889)) (n := 12)
    (lo := (327790239 / 500000000)) (hi := (655580479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1329) = 1/(1329 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-655580479 / 1000000000) (-327790239 / 500000000) (Real.log (1329 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (15689073 / 40000000) ≤ -Real.log (5120 / 7579) ∧
    -Real.log (5120 / 7579) ≤ (196113413 / 500000000) := by
  have h := checkLog_sound (w := (2459 / 12699)) (n := 12)
    (lo := (15689073 / 40000000)) (hi := (196113413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7579 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7579 / 5120) = 1/(5120 / 7579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (15689073 / 40000000) (196113413 / 500000000) (Real.log (7579 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7579 / 5120) = -Real.log (5120 / 7579) := by
    rw [show ((7579 / 5120) : ℝ) = ((5120 / 7579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (654452447 / 1000000000) ≤ -Real.log (2661 / 5120) ∧
    -Real.log (2661 / 5120) ≤ (20451639 / 31250000) := by
  have h := checkLog_sound (w := (2459 / 7781)) (n := 12)
    (lo := (654452447 / 1000000000)) (hi := (20451639 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2661) = 1/(2661 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-20451639 / 31250000) (-654452447 / 1000000000) (Real.log (2661 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (147536719 / 500000000) ≤ -Real.log (40000 / 53729) ∧
    -Real.log (40000 / 53729) ≤ (295073439 / 1000000000) := by
  have h := checkLog_sound (w := (13729 / 93729)) (n := 12)
    (lo := (147536719 / 500000000)) (hi := (295073439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53729 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53729 / 40000) = 1/(40000 / 53729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (147536719 / 500000000) (295073439 / 1000000000) (Real.log (53729 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (53729 / 40000) = -Real.log (40000 / 53729) := by
    rw [show ((53729 / 40000) : ℝ) = ((40000 / 53729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (52551723 / 125000000) ≤ -Real.log (26271 / 40000) ∧
    -Real.log (26271 / 40000) ≤ (84082757 / 200000000) := by
  have h := checkLog_sound (w := (13729 / 66271)) (n := 12)
    (lo := (52551723 / 125000000)) (hi := (84082757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 26271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 26271) = 1/(26271 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-84082757 / 200000000) (-52551723 / 125000000) (Real.log (26271 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (36924189 / 125000000) ≤ -Real.log (200000 / 268731) ∧
    -Real.log (200000 / 268731) ≤ (295393513 / 1000000000) := by
  have h := checkLog_sound (w := (68731 / 468731)) (n := 12)
    (lo := (36924189 / 125000000)) (hi := (295393513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((268731 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(268731 / 200000) = 1/(200000 / 268731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (36924189 / 125000000) (295393513 / 1000000000) (Real.log (268731 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (268731 / 200000) = -Real.log (200000 / 268731) := by
    rw [show ((268731 / 200000) : ℝ) = ((200000 / 268731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (421068713 / 1000000000) ≤ -Real.log (131269 / 200000) ∧
    -Real.log (131269 / 200000) ≤ (210534357 / 500000000) := by
  have h := checkLog_sound (w := (68731 / 331269)) (n := 12)
    (lo := (421068713 / 1000000000)) (hi := (210534357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 131269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 131269) = 1/(131269 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-210534357 / 500000000) (-421068713 / 1000000000) (Real.log (131269 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (111921653 / 500000000) ≤ -Real.log (8000 / 10007) ∧
    -Real.log (8000 / 10007) ≤ (223843307 / 1000000000) := by
  have h := checkLog_sound (w := (2007 / 18007)) (n := 12)
    (lo := (111921653 / 500000000)) (hi := (223843307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10007 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10007 / 8000) = 1/(8000 / 10007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (111921653 / 500000000) (223843307 / 1000000000) (Real.log (10007 / 8000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (10007 / 8000) = -Real.log (8000 / 10007) := by
    rw [show ((10007 / 8000) : ℝ) = ((8000 / 10007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (14442471 / 50000000) ≤ -Real.log (5993 / 8000) ∧
    -Real.log (5993 / 8000) ≤ (288849421 / 1000000000) := by
  have h := checkLog_sound (w := (2007 / 13993)) (n := 12)
    (lo := (14442471 / 50000000)) (hi := (288849421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 5993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 5993) = 1/(5993 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-288849421 / 1000000000) (-14442471 / 50000000) (Real.log (5993 / 8000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (224111083 / 1000000000) ≤ -Real.log (100000 / 125121) ∧
    -Real.log (100000 / 125121) ≤ (56027771 / 250000000) := by
  have h := checkLog_sound (w := (25121 / 225121)) (n := 12)
    (lo := (224111083 / 1000000000)) (hi := (56027771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125121 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125121 / 100000) = 1/(100000 / 125121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (224111083 / 1000000000) (56027771 / 250000000) (Real.log (125121 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (125121 / 100000) = -Real.log (100000 / 125121) := by
    rw [show ((125121 / 100000) : ℝ) = ((100000 / 125121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (72324177 / 250000000) ≤ -Real.log (74879 / 100000) ∧
    -Real.log (74879 / 100000) ≤ (289296709 / 1000000000) := by
  have h := checkLog_sound (w := (25121 / 174879)) (n := 12)
    (lo := (72324177 / 250000000)) (hi := (289296709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 74879) = 1/(74879 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-289296709 / 1000000000) (-72324177 / 250000000) (Real.log (74879 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (715487223 / 1000000000) ≤ -Real.log (500000000000 / 1022591450649) ∧
    -Real.log (500000000000 / 1022591450649) ≤ (28619489 / 40000000) := by
  have h := checkLog_sound (w := (22591450649 / 2022591450649)) (n := 12)
    (lo := (22340043 / 1000000000)) (hi := (5585011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1022591450649 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1022591450649 / 1000000000000) = 1/(500000000000 / 1022591450649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (715487223 / 1000000000) (28619489 / 40000000) (Real.log (1022591450649 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1022591450649 / 500000000000) = -Real.log (500000000000 / 1022591450649) := by
    rw [show ((1022591450649 / 500000000000) : ℝ) = ((500000000000 / 1022591450649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (28658489 / 40000000) ≤ -Real.log (500000000000 / 1023588966169) ∧
    -Real.log (500000000000 / 1023588966169) ≤ (716462227 / 1000000000) := by
  have h := checkLog_sound (w := (23588966169 / 2023588966169)) (n := 12)
    (lo := (4663009 / 200000000)) (hi := (11657523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1023588966169 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1023588966169 / 1000000000000) = 1/(500000000000 / 1023588966169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (28658489 / 40000000) (716462227 / 1000000000) (Real.log (1023588966169 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1023588966169 / 500000000000) = -Real.log (500000000000 / 1023588966169) := by
    rw [show ((1023588966169 / 500000000000) : ℝ) = ((500000000000 / 1023588966169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (256346363 / 500000000) ≤ -Real.log (500000000000 / 834890705823) ∧
    -Real.log (500000000000 / 834890705823) ≤ (512692727 / 1000000000) := by
  have h := checkLog_sound (w := (334890705823 / 1334890705823)) (n := 12)
    (lo := (256346363 / 500000000)) (hi := (512692727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((834890705823 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(834890705823 / 500000000000) = 1/(500000000000 / 834890705823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (256346363 / 500000000) (512692727 / 1000000000) (Real.log (834890705823 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (834890705823 / 500000000000) = -Real.log (500000000000 / 834890705823) := by
    rw [show ((834890705823 / 500000000000) : ℝ) = ((500000000000 / 834890705823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (513407791 / 1000000000) ≤ -Real.log (3906250000 / 6527249379) ∧
    -Real.log (3906250000 / 6527249379) ≤ (32087987 / 62500000) := by
  have h := checkLog_sound (w := (2620999379 / 10433499379)) (n := 12)
    (lo := (513407791 / 1000000000)) (hi := (32087987 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6527249379 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6527249379 / 3906250000) = 1/(3906250000 / 6527249379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (513407791 / 1000000000) (32087987 / 62500000) (Real.log (6527249379 / 3906250000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6527249379 / 3906250000) = -Real.log (3906250000 / 6527249379) := by
    rw [show ((6527249379 / 3906250000) : ℝ) = ((3906250000 / 6527249379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0336
