import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0302
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

theorem reflection_log_1_neg : (111728001 / 500000000) ≤ -Real.log (2560 / 3201) ∧
    -Real.log (2560 / 3201) ≤ (223456003 / 1000000000) := by
  have h := checkLog_sound (w := (641 / 5761)) (n := 12)
    (lo := (111728001 / 500000000)) (hi := (223456003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3201 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3201 / 2560) = 1/(2560 / 3201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (111728001 / 500000000) (223456003 / 1000000000) (Real.log (3201 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3201 / 2560) = -Real.log (2560 / 3201) := by
    rw [show ((3201 / 2560) : ℝ) = ((2560 / 3201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (288203041 / 1000000000) ≤ -Real.log (1919 / 2560) ∧
    -Real.log (1919 / 2560) ≤ (144101521 / 500000000) := by
  have h := checkLog_sound (w := (641 / 4479)) (n := 12)
    (lo := (288203041 / 1000000000)) (hi := (144101521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1919) = 1/(1919 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-144101521 / 500000000) (-288203041 / 1000000000) (Real.log (1919 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (223221673 / 1000000000) ≤ -Real.log (10240 / 12801) ∧
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


theorem reflection_log_3 : Bounds (223221673 / 1000000000) (111610837 / 500000000) (Real.log (12801 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12801 / 10240) = -Real.log (10240 / 12801) := by
    rw [show ((12801 / 10240) : ℝ) = ((10240 / 12801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (287812289 / 1000000000) ≤ -Real.log (7679 / 10240) ∧
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


theorem reflection_log_4 : Bounds (-28781229 / 100000000) (-287812289 / 1000000000) (Real.log (7679 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (81197161 / 200000000) ≤ -Real.log (1280 / 1921) ∧
    -Real.log (1280 / 1921) ≤ (202992903 / 500000000) := by
  have h := checkLog_sound (w := (641 / 3201)) (n := 12)
    (lo := (81197161 / 200000000)) (hi := (202992903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1921 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1921 / 1280) = 1/(1280 / 1921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (81197161 / 200000000) (202992903 / 500000000) (Real.log (1921 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1921 / 1280) = -Real.log (1280 / 1921) := by
    rw [show ((1921 / 1280) : ℝ) = ((1280 / 1921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (694710901 / 1000000000) ≤ -Real.log (639 / 1280) ∧
    -Real.log (639 / 1280) ≤ (694710903 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 1279)) (n := 12)
    (lo := (1563721 / 1000000000)) (hi := (781861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 639) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 639) = 1/(639 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-694710903 / 1000000000) (-694710901 / 1000000000) (Real.log (639 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (405595307 / 1000000000) ≤ -Real.log (5120 / 7681) ∧
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


theorem reflection_log_7 : Bounds (405595307 / 1000000000) (101398827 / 250000000) (Real.log (7681 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7681 / 5120) = -Real.log (5120 / 7681) := by
    rw [show ((7681 / 5120) : ℝ) = ((5120 / 7681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (693537881 / 1000000000) ≤ -Real.log (2559 / 5120) ∧
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


theorem reflection_log_8 : Bounds (-693537883 / 1000000000) (-693537881 / 1000000000) (Real.log (2559 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (61176389 / 200000000) ≤ -Real.log (500000 / 678911) ∧
    -Real.log (500000 / 678911) ≤ (152940973 / 500000000) := by
  have h := checkLog_sound (w := (178911 / 1178911)) (n := 12)
    (lo := (61176389 / 200000000)) (hi := (152940973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678911 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678911 / 500000) = 1/(500000 / 678911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (61176389 / 200000000) (152940973 / 500000000) (Real.log (678911 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (678911 / 500000) = -Real.log (500000 / 678911) := by
    rw [show ((678911 / 500000) : ℝ) = ((500000 / 678911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (88577951 / 200000000) ≤ -Real.log (321089 / 500000) ∧
    -Real.log (321089 / 500000) ≤ (110722439 / 250000000) := by
  have h := checkLog_sound (w := (178911 / 821089)) (n := 12)
    (lo := (88577951 / 200000000)) (hi := (110722439 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 321089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 321089) = 1/(321089 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-110722439 / 250000000) (-88577951 / 200000000) (Real.log (321089 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (61239863 / 200000000) ≤ -Real.log (1000000 / 1358253) ∧
    -Real.log (1000000 / 1358253) ≤ (76549829 / 250000000) := by
  have h := checkLog_sound (w := (358253 / 2358253)) (n := 12)
    (lo := (61239863 / 200000000)) (hi := (76549829 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1358253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1358253 / 1000000) = 1/(1000000 / 1358253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (61239863 / 200000000) (76549829 / 250000000) (Real.log (1358253 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1358253 / 1000000) = -Real.log (1000000 / 1358253) := by
    rw [show ((1358253 / 1000000) : ℝ) = ((1000000 / 1358253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (443561133 / 1000000000) ≤ -Real.log (641747 / 1000000) ∧
    -Real.log (641747 / 1000000) ≤ (221780567 / 500000000) := by
  have h := checkLog_sound (w := (358253 / 1641747)) (n := 12)
    (lo := (443561133 / 1000000000)) (hi := (221780567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 641747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 641747) = 1/(641747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-221780567 / 500000000) (-443561133 / 1000000000) (Real.log (641747 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (1863547 / 8000000) ≤ -Real.log (100000 / 126231) ∧
    -Real.log (100000 / 126231) ≤ (14558961 / 62500000) := by
  have h := checkLog_sound (w := (26231 / 226231)) (n := 12)
    (lo := (1863547 / 8000000)) (hi := (14558961 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126231 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(126231 / 100000) = 1/(100000 / 126231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (1863547 / 8000000) (14558961 / 62500000) (Real.log (126231 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (126231 / 100000) = -Real.log (100000 / 126231) := by
    rw [show ((126231 / 100000) : ℝ) = ((100000 / 126231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (76057899 / 250000000) ≤ -Real.log (73769 / 100000) ∧
    -Real.log (73769 / 100000) ≤ (304231597 / 1000000000) := by
  have h := checkLog_sound (w := (26231 / 173769)) (n := 12)
    (lo := (76057899 / 250000000)) (hi := (304231597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 73769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 73769) = 1/(73769 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-304231597 / 1000000000) (-76057899 / 250000000) (Real.log (73769 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (46642379 / 200000000) ≤ -Real.log (1000000 / 1262649) ∧
    -Real.log (1000000 / 1262649) ≤ (29151487 / 125000000) := by
  have h := checkLog_sound (w := (262649 / 2262649)) (n := 12)
    (lo := (46642379 / 200000000)) (hi := (29151487 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1262649 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1262649 / 1000000) = 1/(1000000 / 1262649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (46642379 / 200000000) (29151487 / 125000000) (Real.log (1262649 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1262649 / 1000000) = -Real.log (1000000 / 1262649) := by
    rw [show ((1262649 / 1000000) : ℝ) = ((1000000 / 1262649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (60938249 / 200000000) ≤ -Real.log (737351 / 1000000) ∧
    -Real.log (737351 / 1000000) ≤ (152345623 / 500000000) := by
  have h := checkLog_sound (w := (262649 / 1737351)) (n := 12)
    (lo := (60938249 / 200000000)) (hi := (152345623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 737351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 737351) = 1/(737351 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-152345623 / 500000000) (-60938249 / 200000000) (Real.log (737351 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (7487717 / 10000000) ≤ -Real.log (125000000000 / 264300162883) ∧
    -Real.log (125000000000 / 264300162883) ≤ (374385851 / 500000000) := by
  have h := checkLog_sound (w := (14300162883 / 514300162883)) (n := 12)
    (lo := (1390613 / 25000000)) (hi := (55624521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((264300162883 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(264300162883 / 250000000000) = 1/(125000000000 / 264300162883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (7487717 / 10000000) (374385851 / 500000000) (Real.log (264300162883 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (264300162883 / 125000000000) = -Real.log (125000000000 / 264300162883) := by
    rw [show ((264300162883 / 125000000000) : ℝ) = ((125000000000 / 264300162883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (11715007 / 15625000) ≤ -Real.log (250000000000 / 529123237039) ∧
    -Real.log (250000000000 / 529123237039) ≤ (14995209 / 20000000) := by
  have h := checkLog_sound (w := (29123237039 / 1029123237039)) (n := 12)
    (lo := (14153317 / 250000000)) (hi := (56613269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((529123237039 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(529123237039 / 500000000000) = 1/(250000000000 / 529123237039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (11715007 / 15625000) (14995209 / 20000000) (Real.log (529123237039 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (529123237039 / 250000000000) = -Real.log (250000000000 / 529123237039) := by
    rw [show ((529123237039 / 250000000000) : ℝ) = ((250000000000 / 529123237039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (134293743 / 250000000) ≤ -Real.log (100000000000 / 171116593691) ∧
    -Real.log (100000000000 / 171116593691) ≤ (537174973 / 1000000000) := by
  have h := checkLog_sound (w := (71116593691 / 271116593691)) (n := 12)
    (lo := (134293743 / 250000000)) (hi := (537174973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171116593691 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171116593691 / 100000000000) = 1/(100000000000 / 171116593691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (134293743 / 250000000) (537174973 / 1000000000) (Real.log (171116593691 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (171116593691 / 100000000000) = -Real.log (100000000000 / 171116593691) := by
    rw [show ((171116593691 / 100000000000) : ℝ) = ((100000000000 / 171116593691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (26895157 / 50000000) ≤ -Real.log (62500000000 / 107025775377) ∧
    -Real.log (62500000000 / 107025775377) ≤ (537903141 / 1000000000) := by
  have h := checkLog_sound (w := (44525775377 / 169525775377)) (n := 12)
    (lo := (26895157 / 50000000)) (hi := (537903141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107025775377 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107025775377 / 62500000000) = 1/(62500000000 / 107025775377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (26895157 / 50000000) (537903141 / 1000000000) (Real.log (107025775377 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (107025775377 / 62500000000) = -Real.log (62500000000 / 107025775377) := by
    rw [show ((107025775377 / 62500000000) : ℝ) = ((62500000000 / 107025775377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0302
