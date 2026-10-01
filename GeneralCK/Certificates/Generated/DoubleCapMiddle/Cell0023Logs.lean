import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0023
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

theorem reflection_log_1_neg : (198022943 / 500000000) ≤ -Real.log (640 / 951) ∧
    -Real.log (640 / 951) ≤ (396045887 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 1591)) (n := 12)
    (lo := (198022943 / 500000000)) (hi := (396045887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((951 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(951 / 640) = 1/(640 / 951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (198022943 / 500000000) (396045887 / 1000000000) (Real.log (951 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (951 / 640) = -Real.log (640 / 951) := by
    rw [show ((951 / 640) : ℝ) = ((640 / 951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (26616417 / 40000000) ≤ -Real.log (329 / 640) ∧
    -Real.log (329 / 640) ≤ (332705213 / 500000000) := by
  have h := checkLog_sound (w := (311 / 969)) (n := 12)
    (lo := (26616417 / 40000000)) (hi := (332705213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 329) = 1/(329 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-332705213 / 500000000) (-26616417 / 40000000) (Real.log (329 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (395256931 / 1000000000) ≤ -Real.log (2560 / 3801) ∧
    -Real.log (2560 / 3801) ≤ (98814233 / 250000000) := by
  have h := checkLog_sound (w := (1241 / 6361)) (n := 12)
    (lo := (395256931 / 1000000000)) (hi := (98814233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3801 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3801 / 2560) = 1/(2560 / 3801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (395256931 / 1000000000) (98814233 / 250000000) (Real.log (3801 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3801 / 2560) = -Real.log (2560 / 3801) := by
    rw [show ((3801 / 2560) : ℝ) = ((2560 / 3801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (82891673 / 125000000) ≤ -Real.log (1319 / 2560) ∧
    -Real.log (1319 / 2560) ≤ (132626677 / 200000000) := by
  have h := checkLog_sound (w := (1241 / 3879)) (n := 12)
    (lo := (82891673 / 125000000)) (hi := (132626677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1319) = 1/(1319 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-132626677 / 200000000) (-82891673 / 125000000) (Real.log (1319 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (339492433 / 500000000) ≤ -Real.log (320 / 631) ∧
    -Real.log (320 / 631) ≤ (678984867 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 951)) (n := 12)
    (lo := (339492433 / 500000000)) (hi := (678984867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((631 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(631 / 320) = 1/(320 / 631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (339492433 / 500000000) (678984867 / 1000000000) (Real.log (631 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (631 / 320) = -Real.log (320 / 631) := by
    rw [show ((631 / 320) : ℝ) = ((320 / 631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (714219283 / 200000000) ≤ -Real.log (9 / 320) ∧
    -Real.log (9 / 320) ≤ (3571096421 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10 / 9) = 1/(9 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3571096421 / 1000000000) (-714219283 / 200000000) (Real.log (9 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (67779557 / 100000000) ≤ -Real.log (1280 / 2521) ∧
    -Real.log (1280 / 2521) ≤ (677795571 / 1000000000) := by
  have h := checkLog_sound (w := (1241 / 3801)) (n := 12)
    (lo := (67779557 / 100000000)) (hi := (677795571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2521 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2521 / 1280) = 1/(1280 / 2521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (67779557 / 100000000) (677795571 / 1000000000) (Real.log (2521 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2521 / 1280) = -Real.log (1280 / 2521) := by
    rw [show ((2521 / 1280) : ℝ) = ((1280 / 2521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3491053707 / 1000000000) ≤ -Real.log (39 / 1280) ∧
    -Real.log (39 / 1280) ≤ (3491053713 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 39) = 1/(39 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3491053713 / 1000000000) (-3491053707 / 1000000000) (Real.log (39 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (554116121 / 1000000000) ≤ -Real.log (500000 / 870201) ∧
    -Real.log (500000 / 870201) ≤ (277058061 / 500000000) := by
  have h := checkLog_sound (w := (370201 / 1370201)) (n := 12)
    (lo := (554116121 / 1000000000)) (hi := (277058061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((870201 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(870201 / 500000) = 1/(500000 / 870201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (554116121 / 1000000000) (277058061 / 500000000) (Real.log (870201 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (870201 / 500000) = -Real.log (500000 / 870201) := by
    rw [show ((870201 / 500000) : ℝ) = ((500000 / 870201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1348620997 / 1000000000) ≤ -Real.log (129799 / 500000) ∧
    -Real.log (129799 / 500000) ≤ (1348620999 / 1000000000) := by
  have h := checkLog_sound (w := (120201 / 379799)) (n := 12)
    (lo := (655473817 / 1000000000)) (hi := (327736909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 129799) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 129799) = 1/(129799 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1348620999 / 1000000000) (-1348620997 / 1000000000) (Real.log (129799 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (138900077 / 250000000) ≤ -Real.log (1000000 / 1742987) ∧
    -Real.log (1000000 / 1742987) ≤ (555600309 / 1000000000) := by
  have h := checkLog_sound (w := (742987 / 2742987)) (n := 12)
    (lo := (138900077 / 250000000)) (hi := (555600309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1742987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1742987 / 1000000) = 1/(1000000 / 1742987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (138900077 / 250000000) (555600309 / 1000000000) (Real.log (1742987 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1742987 / 1000000) = -Real.log (1000000 / 1742987) := by
    rw [show ((1742987 / 1000000) : ℝ) = ((1000000 / 1742987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1358628611 / 1000000000) ≤ -Real.log (257013 / 1000000) ∧
    -Real.log (257013 / 1000000) ≤ (1358628613 / 1000000000) := by
  have h := checkLog_sound (w := (242987 / 757013)) (n := 12)
    (lo := (665481431 / 1000000000)) (hi := (83185179 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 257013) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 257013) = 1/(257013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1358628613 / 1000000000) (-1358628611 / 1000000000) (Real.log (257013 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (479384491 / 1000000000) ≤ -Real.log (25000 / 40377) ∧
    -Real.log (25000 / 40377) ≤ (119846123 / 250000000) := by
  have h := checkLog_sound (w := (15377 / 65377)) (n := 12)
    (lo := (479384491 / 1000000000)) (hi := (119846123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40377 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40377 / 25000) = 1/(25000 / 40377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (479384491 / 1000000000) (119846123 / 250000000) (Real.log (40377 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (40377 / 25000) = -Real.log (25000 / 40377) := by
    rw [show ((40377 / 25000) : ℝ) = ((25000 / 40377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (954719757 / 1000000000) ≤ -Real.log (9623 / 25000) ∧
    -Real.log (9623 / 25000) ≤ (954719759 / 1000000000) := by
  have h := checkLog_sound (w := (2877 / 22123)) (n := 12)
    (lo := (261572577 / 1000000000)) (hi := (130786289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9623) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12500 / 9623) = 1/(9623 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-954719759 / 1000000000) (-954719757 / 1000000000) (Real.log (9623 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (15035919 / 31250000) ≤ -Real.log (1000000 / 1617933) ∧
    -Real.log (1000000 / 1617933) ≤ (481149409 / 1000000000) := by
  have h := checkLog_sound (w := (617933 / 2617933)) (n := 12)
    (lo := (15035919 / 31250000)) (hi := (481149409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1617933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1617933 / 1000000) = 1/(1000000 / 1617933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (15035919 / 31250000) (481149409 / 1000000000) (Real.log (1617933 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1617933 / 1000000) = -Real.log (1000000 / 1617933) := by
    rw [show ((1617933 / 1000000) : ℝ) = ((1000000 / 1617933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (240539823 / 250000000) ≤ -Real.log (382067 / 1000000) ∧
    -Real.log (382067 / 1000000) ≤ (481079647 / 500000000) := by
  have h := checkLog_sound (w := (117933 / 882067)) (n := 12)
    (lo := (16813257 / 62500000)) (hi := (269012113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 382067) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 382067) = 1/(382067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-481079647 / 500000000) (-240539823 / 250000000) (Real.log (382067 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (951368559 / 500000000) ≤ -Real.log (500000000000 / 3352109800537) ∧
    -Real.log (500000000000 / 3352109800537) ≤ (1902737121 / 1000000000) := by
  have h := checkLog_sound (w := (1352109800537 / 5352109800537)) (n := 12)
    (lo := (258221379 / 500000000)) (hi := (516442759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3352109800537 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3352109800537 / 2000000000000) = 1/(500000000000 / 3352109800537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (951368559 / 500000000) (1902737121 / 1000000000) (Real.log (3352109800537 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3352109800537 / 500000000000) = -Real.log (500000000000 / 3352109800537) := by
    rw [show ((3352109800537 / 500000000000) : ℝ) = ((500000000000 / 3352109800537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (957114459 / 500000000) ≤ -Real.log (500000000000 / 3390853770043) ∧
    -Real.log (500000000000 / 3390853770043) ≤ (1914228921 / 1000000000) := by
  have h := checkLog_sound (w := (1390853770043 / 5390853770043)) (n := 12)
    (lo := (263967279 / 500000000)) (hi := (527934559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3390853770043 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3390853770043 / 2000000000000) = 1/(500000000000 / 3390853770043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (957114459 / 500000000) (1914228921 / 1000000000) (Real.log (3390853770043 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3390853770043 / 500000000000) = -Real.log (500000000000 / 3390853770043) := by
    rw [show ((3390853770043 / 500000000000) : ℝ) = ((500000000000 / 3390853770043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (179263031 / 125000000) ≤ -Real.log (100000000000 / 419588485919) ∧
    -Real.log (100000000000 / 419588485919) ≤ (1434104251 / 1000000000) := by
  have h := checkLog_sound (w := (19588485919 / 819588485919)) (n := 12)
    (lo := (1494059 / 31250000)) (hi := (47809889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419588485919 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(419588485919 / 400000000000) = 1/(100000000000 / 419588485919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (179263031 / 125000000) (1434104251 / 1000000000) (Real.log (419588485919 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (419588485919 / 100000000000) = -Real.log (100000000000 / 419588485919) := by
    rw [show ((419588485919 / 100000000000) : ℝ) = ((100000000000 / 419588485919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (14433087 / 10000000) ≤ -Real.log (250000000000 / 1058670992261) ∧
    -Real.log (250000000000 / 1058670992261) ≤ (1443308703 / 1000000000) := by
  have h := checkLog_sound (w := (58670992261 / 2058670992261)) (n := 12)
    (lo := (2850717 / 50000000)) (hi := (57014341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1058670992261 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1058670992261 / 1000000000000) = 1/(250000000000 / 1058670992261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (14433087 / 10000000) (1443308703 / 1000000000) (Real.log (1058670992261 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1058670992261 / 250000000000) = -Real.log (250000000000 / 1058670992261) := by
    rw [show ((1058670992261 / 250000000000) : ℝ) = ((250000000000 / 1058670992261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0023
