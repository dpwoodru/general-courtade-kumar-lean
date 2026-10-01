import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell204
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

theorem reflection_log_1_neg : (157448137 / 500000000) ≤ -Real.log (1024 / 1403) ∧
    -Real.log (1024 / 1403) ≤ (12595851 / 40000000) := by
  have h := checkLog_sound (w := (379 / 2427)) (n := 12)
    (lo := (157448137 / 500000000)) (hi := (12595851 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1403 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1403 / 1024) = 1/(1024 / 1403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (157448137 / 500000000) (12595851 / 40000000) (Real.log (1403 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1403 / 1024) = -Real.log (1024 / 1403) := by
    rw [show ((1403 / 1024) : ℝ) = ((1024 / 1403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (28888843 / 62500000) ≤ -Real.log (645 / 1024) ∧
    -Real.log (645 / 1024) ≤ (462221489 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 1669)) (n := 12)
    (lo := (28888843 / 62500000)) (hi := (462221489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 645) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 645) = 1/(645 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-462221489 / 1000000000) (-28888843 / 62500000) (Real.log (645 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (19654283 / 62500000) ≤ -Real.log (1280 / 1753) ∧
    -Real.log (1280 / 1753) ≤ (314468529 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 3033)) (n := 12)
    (lo := (19654283 / 62500000)) (hi := (314468529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1753 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1753 / 1280) = 1/(1280 / 1753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (19654283 / 62500000) (314468529 / 1000000000) (Real.log (1753 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1753 / 1280) = -Real.log (1280 / 1753) := by
    rw [show ((1753 / 1280) : ℝ) = ((1280 / 1753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (57661461 / 125000000) ≤ -Real.log (807 / 1280) ∧
    -Real.log (807 / 1280) ≤ (461291689 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 2087)) (n := 12)
    (lo := (57661461 / 125000000)) (hi := (461291689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 807) = 1/(807 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-461291689 / 1000000000) (-57661461 / 125000000) (Real.log (807 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (233390867 / 1000000000) ≤ -Real.log (8000 / 10103) ∧
    -Real.log (8000 / 10103) ≤ (58347717 / 250000000) := by
  have h := checkLog_sound (w := (2103 / 18103)) (n := 12)
    (lo := (233390867 / 1000000000)) (hi := (58347717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10103 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10103 / 8000) = 1/(8000 / 10103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (233390867 / 1000000000) (58347717 / 250000000) (Real.log (10103 / 8000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (10103 / 8000) = -Real.log (8000 / 10103) := by
    rw [show ((10103 / 8000) : ℝ) = ((8000 / 10103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (152498897 / 500000000) ≤ -Real.log (5897 / 8000) ∧
    -Real.log (5897 / 8000) ≤ (60999559 / 200000000) := by
  have h := checkLog_sound (w := (2103 / 13897)) (n := 12)
    (lo := (152498897 / 500000000)) (hi := (60999559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 5897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 5897) = 1/(5897 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-60999559 / 200000000) (-152498897 / 500000000) (Real.log (5897 / 8000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (233725761 / 1000000000) ≤ -Real.log (500000 / 631649) ∧
    -Real.log (500000 / 631649) ≤ (116862881 / 500000000) := by
  have h := checkLog_sound (w := (131649 / 1131649)) (n := 12)
    (lo := (233725761 / 1000000000)) (hi := (116862881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((631649 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(631649 / 500000) = 1/(500000 / 631649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (233725761 / 1000000000) (116862881 / 500000000) (Real.log (631649 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (631649 / 500000) = -Real.log (500000 / 631649) := by
    rw [show ((631649 / 500000) : ℝ) = ((500000 / 631649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (30557181 / 100000000) ≤ -Real.log (368351 / 500000) ∧
    -Real.log (368351 / 500000) ≤ (305571811 / 1000000000) := by
  have h := checkLog_sound (w := (131649 / 868351)) (n := 12)
    (lo := (30557181 / 100000000)) (hi := (305571811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 368351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 368351) = 1/(368351 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-305571811 / 1000000000) (-30557181 / 100000000) (Real.log (368351 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2711559 / 15625000) ≤ -Real.log (250000 / 297377) ∧
    -Real.log (250000 / 297377) ≤ (173539777 / 1000000000) := by
  have h := checkLog_sound (w := (47377 / 547377)) (n := 12)
    (lo := (2711559 / 15625000)) (hi := (173539777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297377 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297377 / 250000) = 1/(250000 / 297377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2711559 / 15625000) (173539777 / 1000000000) (Real.log (297377 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (297377 / 250000) = -Real.log (250000 / 297377) := by
    rw [show ((297377 / 250000) : ℝ) = ((250000 / 297377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (13132113 / 62500000) ≤ -Real.log (202623 / 250000) ∧
    -Real.log (202623 / 250000) ≤ (210113809 / 1000000000) := by
  have h := checkLog_sound (w := (47377 / 452623)) (n := 12)
    (lo := (13132113 / 62500000)) (hi := (210113809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 202623) = 1/(202623 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-210113809 / 1000000000) (-13132113 / 62500000) (Real.log (202623 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (173806237 / 1000000000) ≤ -Real.log (40000 / 47593) ∧
    -Real.log (40000 / 47593) ≤ (86903119 / 500000000) := by
  have h := checkLog_sound (w := (7593 / 87593)) (n := 12)
    (lo := (173806237 / 1000000000)) (hi := (86903119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47593 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47593 / 40000) = 1/(40000 / 47593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (173806237 / 1000000000) (86903119 / 500000000) (Real.log (47593 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (47593 / 40000) = -Real.log (40000 / 47593) := by
    rw [show ((47593 / 40000) : ℝ) = ((40000 / 47593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (42101001 / 200000000) ≤ -Real.log (32407 / 40000) ∧
    -Real.log (32407 / 40000) ≤ (105252503 / 500000000) := by
  have h := checkLog_sound (w := (7593 / 72407)) (n := 12)
    (lo := (42101001 / 200000000)) (hi := (105252503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 32407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 32407) = 1/(32407 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-105252503 / 500000000) (-42101001 / 200000000) (Real.log (32407 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (96970027 / 125000000) ≤ -Real.log (250000000000 / 543060718711) ∧
    -Real.log (250000000000 / 543060718711) ≤ (387880109 / 500000000) := by
  have h := checkLog_sound (w := (43060718711 / 1043060718711)) (n := 12)
    (lo := (20653259 / 250000000)) (hi := (82613037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543060718711 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(543060718711 / 500000000000) = 1/(250000000000 / 543060718711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (96970027 / 125000000) (387880109 / 500000000) (Real.log (543060718711 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (543060718711 / 250000000000) = -Real.log (250000000000 / 543060718711) := by
    rw [show ((543060718711 / 250000000000) : ℝ) = ((250000000000 / 543060718711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (388558881 / 500000000) ≤ -Real.log (20000000000 / 43503875969) ∧
    -Real.log (20000000000 / 43503875969) ≤ (194279441 / 250000000) := by
  have h := checkLog_sound (w := (3503875969 / 83503875969)) (n := 12)
    (lo := (41985291 / 500000000)) (hi := (83970583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43503875969 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(43503875969 / 40000000000) = 1/(20000000000 / 43503875969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (388558881 / 500000000) (194279441 / 250000000) (Real.log (43503875969 / 20000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (43503875969 / 20000000000) = -Real.log (20000000000 / 43503875969) := by
    rw [show ((43503875969 / 20000000000) : ℝ) = ((20000000000 / 43503875969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (269194331 / 500000000) ≤ -Real.log (62500000000 / 107077751399) ∧
    -Real.log (62500000000 / 107077751399) ≤ (538388663 / 1000000000) := by
  have h := checkLog_sound (w := (44577751399 / 169577751399)) (n := 12)
    (lo := (269194331 / 500000000)) (hi := (538388663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107077751399 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107077751399 / 62500000000) = 1/(62500000000 / 107077751399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (269194331 / 500000000) (538388663 / 1000000000) (Real.log (107077751399 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (107077751399 / 62500000000) = -Real.log (62500000000 / 107077751399) := by
    rw [show ((107077751399 / 62500000000) : ℝ) = ((62500000000 / 107077751399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (134824393 / 250000000) ≤ -Real.log (12500000000 / 21435023931) ∧
    -Real.log (12500000000 / 21435023931) ≤ (539297573 / 1000000000) := by
  have h := checkLog_sound (w := (8935023931 / 33935023931)) (n := 12)
    (lo := (134824393 / 250000000)) (hi := (539297573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21435023931 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21435023931 / 12500000000) = 1/(12500000000 / 21435023931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (134824393 / 250000000) (539297573 / 1000000000) (Real.log (21435023931 / 12500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (21435023931 / 12500000000) = -Real.log (12500000000 / 21435023931) := by
    rw [show ((21435023931 / 12500000000) : ℝ) = ((12500000000 / 21435023931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (23978349 / 62500000) ≤ -Real.log (125000000000 / 183454617689) ∧
    -Real.log (125000000000 / 183454617689) ≤ (76730717 / 200000000) := by
  have h := checkLog_sound (w := (58454617689 / 308454617689)) (n := 12)
    (lo := (23978349 / 62500000)) (hi := (76730717 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183454617689 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183454617689 / 125000000000) = 1/(125000000000 / 183454617689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (23978349 / 62500000) (76730717 / 200000000) (Real.log (183454617689 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (183454617689 / 125000000000) = -Real.log (125000000000 / 183454617689) := by
    rw [show ((183454617689 / 125000000000) : ℝ) = ((125000000000 / 183454617689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (192155621 / 500000000) ≤ -Real.log (31250000000 / 45893826951) ∧
    -Real.log (31250000000 / 45893826951) ≤ (384311243 / 1000000000) := by
  have h := checkLog_sound (w := (14643826951 / 77143826951)) (n := 12)
    (lo := (192155621 / 500000000)) (hi := (384311243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45893826951 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45893826951 / 31250000000) = 1/(31250000000 / 45893826951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (192155621 / 500000000) (384311243 / 1000000000) (Real.log (45893826951 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (45893826951 / 31250000000) = -Real.log (31250000000 / 45893826951) := by
    rw [show ((45893826951 / 31250000000) : ℝ) = ((31250000000 / 45893826951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (36698767 / 1000000000) ≤ -Real.log (1542346351 / 1600000000) ∧
    -Real.log (1542346351 / 1600000000) ≤ (2293673 / 62500000) := by
  have h := checkLog_sound (w := (57653649 / 3142346351)) (n := 12)
    (lo := (36698767 / 1000000000)) (hi := (2293673 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1542346351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1542346351) = 1/(1542346351 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2293673 / 62500000) (-36698767 / 1000000000) (Real.log (1542346351 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2285877 / 62500000) ≤ -Real.log (60255419871 / 62500000000) ∧
    -Real.log (60255419871 / 62500000000) ≤ (36574033 / 1000000000) := by
  have h := checkLog_sound (w := (2244580129 / 122755419871)) (n := 12)
    (lo := (2285877 / 62500000)) (hi := (36574033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60255419871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60255419871) = 1/(60255419871 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-36574033 / 1000000000) (-2285877 / 62500000) (Real.log (60255419871 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell204
