import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0424
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

theorem reflection_log_1_neg : (194454683 / 1000000000) ≤ -Real.log (5120 / 6219) ∧
    -Real.log (5120 / 6219) ≤ (48613671 / 250000000) := by
  have h := checkLog_sound (w := (1099 / 11339)) (n := 12)
    (lo := (194454683 / 1000000000)) (hi := (48613671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6219 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6219 / 5120) = 1/(5120 / 6219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (194454683 / 1000000000) (48613671 / 250000000) (Real.log (6219 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6219 / 5120) = -Real.log (5120 / 6219) := by
    rw [show ((6219 / 5120) : ℝ) = ((5120 / 6219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (241623811 / 1000000000) ≤ -Real.log (4021 / 5120) ∧
    -Real.log (4021 / 5120) ≤ (60405953 / 250000000) := by
  have h := checkLog_sound (w := (1099 / 9141)) (n := 12)
    (lo := (241623811 / 1000000000)) (hi := (60405953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4021) = 1/(4021 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-60405953 / 250000000) (-241623811 / 1000000000) (Real.log (4021 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (194213457 / 1000000000) ≤ -Real.log (2048 / 2487) ∧
    -Real.log (2048 / 2487) ≤ (97106729 / 500000000) := by
  have h := checkLog_sound (w := (439 / 4535)) (n := 12)
    (lo := (194213457 / 1000000000)) (hi := (97106729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2487 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2487 / 2048) = 1/(2048 / 2487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (194213457 / 1000000000) (97106729 / 500000000) (Real.log (2487 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2487 / 2048) = -Real.log (2048 / 2487) := by
    rw [show ((2487 / 2048) : ℝ) = ((2048 / 2487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (241250839 / 1000000000) ≤ -Real.log (1609 / 2048) ∧
    -Real.log (1609 / 2048) ≤ (6031271 / 25000000) := by
  have h := checkLog_sound (w := (439 / 3657)) (n := 12)
    (lo := (241250839 / 1000000000)) (hi := (6031271 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1609) = 1/(1609 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6031271 / 25000000) (-241250839 / 1000000000) (Real.log (1609 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (357182627 / 1000000000) ≤ -Real.log (2560 / 3659) ∧
    -Real.log (2560 / 3659) ≤ (89295657 / 250000000) := by
  have h := checkLog_sound (w := (1099 / 6219)) (n := 12)
    (lo := (357182627 / 1000000000)) (hi := (89295657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3659 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3659 / 2560) = 1/(2560 / 3659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (357182627 / 1000000000) (89295657 / 250000000) (Real.log (3659 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3659 / 2560) = -Real.log (2560 / 3659) := by
    rw [show ((3659 / 2560) : ℝ) = ((2560 / 3659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (4487089 / 8000000) ≤ -Real.log (1461 / 2560) ∧
    -Real.log (1461 / 2560) ≤ (280443063 / 500000000) := by
  have h := checkLog_sound (w := (1099 / 4021)) (n := 12)
    (lo := (4487089 / 8000000)) (hi := (280443063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1461) = 1/(1461 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-280443063 / 500000000) (-4487089 / 8000000) (Real.log (1461 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (71354519 / 200000000) ≤ -Real.log (1024 / 1463) ∧
    -Real.log (1024 / 1463) ≤ (89193149 / 250000000) := by
  have h := checkLog_sound (w := (439 / 2487)) (n := 12)
    (lo := (71354519 / 200000000)) (hi := (89193149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1463 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1463 / 1024) = 1/(1024 / 1463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (71354519 / 200000000) (89193149 / 250000000) (Real.log (1463 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1463 / 1024) = -Real.log (1024 / 1463) := by
    rw [show ((1463 / 1024) : ℝ) = ((1024 / 1463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (279929979 / 500000000) ≤ -Real.log (585 / 1024) ∧
    -Real.log (585 / 1024) ≤ (559859959 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 1609)) (n := 12)
    (lo := (279929979 / 500000000)) (hi := (559859959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 585) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 585) = 1/(585 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-559859959 / 1000000000) (-279929979 / 500000000) (Real.log (585 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (266710191 / 1000000000) ≤ -Real.log (500000 / 652831) ∧
    -Real.log (500000 / 652831) ≤ (16669387 / 62500000) := by
  have h := checkLog_sound (w := (152831 / 1152831)) (n := 12)
    (lo := (266710191 / 1000000000)) (hi := (16669387 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((652831 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(652831 / 500000) = 1/(500000 / 652831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (266710191 / 1000000000) (16669387 / 62500000) (Real.log (652831 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (652831 / 500000) = -Real.log (500000 / 652831) := by
    rw [show ((652831 / 500000) : ℝ) = ((500000 / 652831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (72959281 / 200000000) ≤ -Real.log (347169 / 500000) ∧
    -Real.log (347169 / 500000) ≤ (182398203 / 500000000) := by
  have h := checkLog_sound (w := (152831 / 847169)) (n := 12)
    (lo := (72959281 / 200000000)) (hi := (182398203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 347169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 347169) = 1/(347169 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-182398203 / 500000000) (-72959281 / 200000000) (Real.log (347169 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (267036409 / 1000000000) ≤ -Real.log (125000 / 163261) ∧
    -Real.log (125000 / 163261) ≤ (26703641 / 100000000) := by
  have h := checkLog_sound (w := (38261 / 288261)) (n := 12)
    (lo := (267036409 / 1000000000)) (hi := (26703641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163261 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163261 / 125000) = 1/(125000 / 163261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (267036409 / 1000000000) (26703641 / 100000000) (Real.log (163261 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (163261 / 125000) = -Real.log (125000 / 163261) := by
    rw [show ((163261 / 125000) : ℝ) = ((125000 / 163261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (365410127 / 1000000000) ≤ -Real.log (86739 / 125000) ∧
    -Real.log (86739 / 125000) ≤ (22838133 / 62500000) := by
  have h := checkLog_sound (w := (38261 / 211739)) (n := 12)
    (lo := (365410127 / 1000000000)) (hi := (22838133 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 86739) = 1/(86739 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-22838133 / 62500000) (-365410127 / 1000000000) (Real.log (86739 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (50096641 / 250000000) ≤ -Real.log (320 / 391) ∧
    -Real.log (320 / 391) ≤ (40077313 / 200000000) := by
  have h := checkLog_sound (w := (71 / 711)) (n := 12)
    (lo := (50096641 / 250000000)) (hi := (40077313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((391 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(391 / 320) = 1/(320 / 391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (50096641 / 250000000) (40077313 / 200000000) (Real.log (391 / 320)) := by
  have h := reflection_log_13_neg
  have he : Real.log (391 / 320) = -Real.log (320 / 391) := by
    rw [show ((391 / 320) : ℝ) = ((320 / 391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (250868099 / 1000000000) ≤ -Real.log (249 / 320) ∧
    -Real.log (249 / 320) ≤ (2508681 / 10000000) := by
  have h := checkLog_sound (w := (71 / 569)) (n := 12)
    (lo := (250868099 / 1000000000)) (hi := (2508681 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 249) = 1/(249 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2508681 / 10000000) (-250868099 / 1000000000) (Real.log (249 / 320)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (200653331 / 1000000000) ≤ -Real.log (1000000 / 1222201) ∧
    -Real.log (1000000 / 1222201) ≤ (50163333 / 250000000) := by
  have h := checkLog_sound (w := (222201 / 2222201)) (n := 12)
    (lo := (200653331 / 1000000000)) (hi := (50163333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1222201 / 1000000) = 1/(1000000 / 1222201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (200653331 / 1000000000) (50163333 / 250000000) (Real.log (1222201 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1222201 / 1000000) = -Real.log (1000000 / 1222201) := by
    rw [show ((1222201 / 1000000) : ℝ) = ((1000000 / 1222201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (125643571 / 500000000) ≤ -Real.log (777799 / 1000000) ∧
    -Real.log (777799 / 1000000) ≤ (251287143 / 1000000000) := by
  have h := checkLog_sound (w := (222201 / 1777799)) (n := 12)
    (lo := (125643571 / 500000000)) (hi := (251287143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 777799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 777799) = 1/(777799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-251287143 / 1000000000) (-125643571 / 500000000) (Real.log (777799 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (631506597 / 1000000000) ≤ -Real.log (500000000000 / 940220757037) ∧
    -Real.log (500000000000 / 940220757037) ≤ (315753299 / 500000000) := by
  have h := checkLog_sound (w := (440220757037 / 1440220757037)) (n := 12)
    (lo := (631506597 / 1000000000)) (hi := (315753299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940220757037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940220757037 / 500000000000) = 1/(500000000000 / 940220757037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (631506597 / 1000000000) (315753299 / 500000000) (Real.log (940220757037 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (940220757037 / 500000000000) = -Real.log (500000000000 / 940220757037) := by
    rw [show ((940220757037 / 500000000000) : ℝ) = ((500000000000 / 940220757037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (632446537 / 1000000000) ≤ -Real.log (7812500000 / 14704764437) ∧
    -Real.log (7812500000 / 14704764437) ≤ (316223269 / 500000000) := by
  have h := checkLog_sound (w := (6892264437 / 22517264437)) (n := 12)
    (lo := (632446537 / 1000000000)) (hi := (316223269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14704764437 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14704764437 / 7812500000) = 1/(7812500000 / 14704764437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (632446537 / 1000000000) (316223269 / 500000000) (Real.log (14704764437 / 7812500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14704764437 / 7812500000) = -Real.log (7812500000 / 14704764437) := by
    rw [show ((14704764437 / 7812500000) : ℝ) = ((7812500000 / 14704764437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (451254663 / 1000000000) ≤ -Real.log (62500000000 / 98142570281) ∧
    -Real.log (62500000000 / 98142570281) ≤ (56406833 / 125000000) := by
  have h := checkLog_sound (w := (35642570281 / 160642570281)) (n := 12)
    (lo := (451254663 / 1000000000)) (hi := (56406833 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98142570281 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98142570281 / 62500000000) = 1/(62500000000 / 98142570281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (451254663 / 1000000000) (56406833 / 125000000) (Real.log (98142570281 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (98142570281 / 62500000000) = -Real.log (62500000000 / 98142570281) := by
    rw [show ((98142570281 / 62500000000) : ℝ) = ((62500000000 / 98142570281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (225970237 / 500000000) ≤ -Real.log (500000000000 / 785679205039) ∧
    -Real.log (500000000000 / 785679205039) ≤ (18077619 / 40000000) := by
  have h := checkLog_sound (w := (285679205039 / 1285679205039)) (n := 12)
    (lo := (225970237 / 500000000)) (hi := (18077619 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((785679205039 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(785679205039 / 500000000000) = 1/(500000000000 / 785679205039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (225970237 / 500000000) (18077619 / 40000000) (Real.log (785679205039 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (785679205039 / 500000000000) = -Real.log (500000000000 / 785679205039) := by
    rw [show ((785679205039 / 500000000000) : ℝ) = ((500000000000 / 785679205039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0424
