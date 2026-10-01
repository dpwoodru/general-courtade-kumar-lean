import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell029
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

theorem reflection_log_1_neg : (237108091 / 1000000000) ≤ -Real.log (512 / 649) ∧
    -Real.log (512 / 649) ≤ (59277023 / 250000000) := by
  have h := checkLog_sound (w := (137 / 1161)) (n := 12)
    (lo := (237108091 / 1000000000)) (hi := (59277023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649 / 512) = 1/(512 / 649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (237108091 / 1000000000) (59277023 / 250000000) (Real.log (649 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (649 / 512) = -Real.log (512 / 649) := by
    rw [show ((649 / 512) : ℝ) = ((512 / 649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (311398599 / 1000000000) ≤ -Real.log (375 / 512) ∧
    -Real.log (375 / 512) ≤ (1556993 / 5000000) := by
  have h := checkLog_sound (w := (137 / 887)) (n := 12)
    (lo := (311398599 / 1000000000)) (hi := (1556993 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 375) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 375) = 1/(375 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1556993 / 5000000) (-311398599 / 1000000000) (Real.log (375 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (47329147 / 200000000) ≤ -Real.log (5120 / 6487) ∧
    -Real.log (5120 / 6487) ≤ (29580717 / 125000000) := by
  have h := checkLog_sound (w := (1367 / 11607)) (n := 12)
    (lo := (47329147 / 200000000)) (hi := (29580717 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6487 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6487 / 5120) = 1/(5120 / 6487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (47329147 / 200000000) (29580717 / 125000000) (Real.log (6487 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6487 / 5120) = -Real.log (5120 / 6487) := by
    rw [show ((6487 / 5120) : ℝ) = ((5120 / 6487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (155299459 / 500000000) ≤ -Real.log (3753 / 5120) ∧
    -Real.log (3753 / 5120) ≤ (310598919 / 1000000000) := by
  have h := checkLog_sound (w := (1367 / 8873)) (n := 12)
    (lo := (155299459 / 500000000)) (hi := (310598919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3753) = 1/(3753 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-310598919 / 1000000000) (-155299459 / 500000000) (Real.log (3753 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (86711457 / 500000000) ≤ -Real.log (1000000 / 1189369) ∧
    -Real.log (1000000 / 1189369) ≤ (34684583 / 200000000) := by
  have h := checkLog_sound (w := (189369 / 2189369)) (n := 12)
    (lo := (86711457 / 500000000)) (hi := (34684583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1189369 / 1000000) = 1/(1000000 / 1189369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (86711457 / 500000000) (34684583 / 200000000) (Real.log (1189369 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1189369 / 1000000) = -Real.log (1000000 / 1189369) := by
    rw [show ((1189369 / 1000000) : ℝ) = ((1000000 / 1189369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (104971161 / 500000000) ≤ -Real.log (810631 / 1000000) ∧
    -Real.log (810631 / 1000000) ≤ (209942323 / 1000000000) := by
  have h := checkLog_sound (w := (189369 / 1810631)) (n := 12)
    (lo := (104971161 / 500000000)) (hi := (209942323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 810631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 810631) = 1/(810631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-209942323 / 1000000000) (-104971161 / 500000000) (Real.log (810631 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (8688799 / 50000000) ≤ -Real.log (1000000 / 1189789) ∧
    -Real.log (1000000 / 1189789) ≤ (173775981 / 1000000000) := by
  have h := checkLog_sound (w := (189789 / 2189789)) (n := 12)
    (lo := (8688799 / 50000000)) (hi := (173775981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1189789 / 1000000) = 1/(1000000 / 1189789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (8688799 / 50000000) (173775981 / 1000000000) (Real.log (1189789 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1189789 / 1000000) = -Real.log (1000000 / 1189789) := by
    rw [show ((1189789 / 1000000) : ℝ) = ((1000000 / 1189789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (210460571 / 1000000000) ≤ -Real.log (810211 / 1000000) ∧
    -Real.log (810211 / 1000000) ≤ (52615143 / 250000000) := by
  have h := checkLog_sound (w := (189789 / 1810211)) (n := 12)
    (lo := (210460571 / 1000000000)) (hi := (52615143 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 810211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 810211) = 1/(810211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-52615143 / 250000000) (-210460571 / 1000000000) (Real.log (810211 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (12685201 / 100000000) ≤ -Real.log (1000000 / 1135249) ∧
    -Real.log (1000000 / 1135249) ≤ (126852011 / 1000000000) := by
  have h := checkLog_sound (w := (135249 / 2135249)) (n := 12)
    (lo := (12685201 / 100000000)) (hi := (126852011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1135249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1135249 / 1000000) = 1/(1000000 / 1135249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (12685201 / 100000000) (126852011 / 1000000000) (Real.log (1135249 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1135249 / 1000000) = -Real.log (1000000 / 1135249) := by
    rw [show ((1135249 / 1000000) : ℝ) = ((1000000 / 1135249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (72656837 / 500000000) ≤ -Real.log (864751 / 1000000) ∧
    -Real.log (864751 / 1000000) ≤ (5812547 / 40000000) := by
  have h := checkLog_sound (w := (135249 / 1864751)) (n := 12)
    (lo := (72656837 / 500000000)) (hi := (5812547 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 864751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 864751) = 1/(864751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-5812547 / 40000000) (-72656837 / 500000000) (Real.log (864751 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (127120637 / 1000000000) ≤ -Real.log (500000 / 567777) ∧
    -Real.log (500000 / 567777) ≤ (63560319 / 500000000) := by
  have h := checkLog_sound (w := (67777 / 1067777)) (n := 12)
    (lo := (127120637 / 1000000000)) (hi := (63560319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567777 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(567777 / 500000) = 1/(500000 / 567777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (127120637 / 1000000000) (63560319 / 500000000) (Real.log (567777 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (567777 / 500000) = -Real.log (500000 / 567777) := by
    rw [show ((567777 / 500000) : ℝ) = ((500000 / 567777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (145666439 / 1000000000) ≤ -Real.log (432223 / 500000) ∧
    -Real.log (432223 / 500000) ≤ (3641661 / 25000000) := by
  have h := checkLog_sound (w := (67777 / 932223)) (n := 12)
    (lo := (145666439 / 1000000000)) (hi := (3641661 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 432223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 432223) = 1/(432223 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3641661 / 25000000) (-145666439 / 1000000000) (Real.log (432223 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (273622327 / 500000000) ≤ -Real.log (500000000000 / 864241939781) ∧
    -Real.log (500000000000 / 864241939781) ≤ (109448931 / 200000000) := by
  have h := checkLog_sound (w := (364241939781 / 1364241939781)) (n := 12)
    (lo := (273622327 / 500000000)) (hi := (109448931 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((864241939781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(864241939781 / 500000000000) = 1/(500000000000 / 864241939781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (273622327 / 500000000) (109448931 / 200000000) (Real.log (864241939781 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (864241939781 / 500000000000) = -Real.log (500000000000 / 864241939781) := by
    rw [show ((864241939781 / 500000000000) : ℝ) = ((500000000000 / 864241939781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (54850669 / 100000000) ≤ -Real.log (250000000000 / 432666666667) ∧
    -Real.log (250000000000 / 432666666667) ≤ (548506691 / 1000000000) := by
  have h := checkLog_sound (w := (182666666667 / 682666666667)) (n := 12)
    (lo := (54850669 / 100000000)) (hi := (548506691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432666666667 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(432666666667 / 250000000000) = 1/(250000000000 / 432666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (54850669 / 100000000) (548506691 / 1000000000) (Real.log (432666666667 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (432666666667 / 250000000000) = -Real.log (250000000000 / 432666666667) := by
    rw [show ((432666666667 / 250000000000) : ℝ) = ((250000000000 / 432666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (95841309 / 250000000) ≤ -Real.log (31250000000 / 45850431639) ∧
    -Real.log (31250000000 / 45850431639) ≤ (383365237 / 1000000000) := by
  have h := checkLog_sound (w := (14600431639 / 77100431639)) (n := 12)
    (lo := (95841309 / 250000000)) (hi := (383365237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45850431639 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45850431639 / 31250000000) = 1/(31250000000 / 45850431639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (95841309 / 250000000) (383365237 / 1000000000) (Real.log (45850431639 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (45850431639 / 31250000000) = -Real.log (31250000000 / 45850431639) := by
    rw [show ((45850431639 / 31250000000) : ℝ) = ((31250000000 / 45850431639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (384236551 / 1000000000) ≤ -Real.log (50000000000 / 73424638767) ∧
    -Real.log (50000000000 / 73424638767) ≤ (48029569 / 125000000) := by
  have h := checkLog_sound (w := (23424638767 / 123424638767)) (n := 12)
    (lo := (384236551 / 1000000000)) (hi := (48029569 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73424638767 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73424638767 / 50000000000) = 1/(50000000000 / 73424638767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (384236551 / 1000000000) (48029569 / 125000000) (Real.log (73424638767 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (73424638767 / 50000000000) = -Real.log (50000000000 / 73424638767) := by
    rw [show ((73424638767 / 50000000000) : ℝ) = ((50000000000 / 73424638767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (68041421 / 250000000) ≤ -Real.log (500000000000 / 656402247583) ∧
    -Real.log (500000000000 / 656402247583) ≤ (54433137 / 200000000) := by
  have h := checkLog_sound (w := (156402247583 / 1156402247583)) (n := 12)
    (lo := (68041421 / 250000000)) (hi := (54433137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((656402247583 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(656402247583 / 500000000000) = 1/(500000000000 / 656402247583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (68041421 / 250000000) (54433137 / 200000000) (Real.log (656402247583 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (656402247583 / 500000000000) = -Real.log (500000000000 / 656402247583) := by
    rw [show ((656402247583 / 500000000000) : ℝ) = ((500000000000 / 656402247583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (272787077 / 1000000000) ≤ -Real.log (125000000000 / 164202564417) ∧
    -Real.log (125000000000 / 164202564417) ≤ (136393539 / 500000000) := by
  have h := checkLog_sound (w := (39202564417 / 289202564417)) (n := 12)
    (lo := (272787077 / 1000000000)) (hi := (136393539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164202564417 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164202564417 / 125000000000) = 1/(125000000000 / 164202564417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (272787077 / 1000000000) (136393539 / 500000000) (Real.log (164202564417 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (164202564417 / 125000000000) = -Real.log (125000000000 / 164202564417) := by
    rw [show ((164202564417 / 125000000000) : ℝ) = ((125000000000 / 164202564417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9272901 / 500000000) ≤ -Real.log (245406278271 / 250000000000) ∧
    -Real.log (245406278271 / 250000000000) ≤ (18545803 / 1000000000) := by
  have h := checkLog_sound (w := (4593721729 / 495406278271)) (n := 12)
    (lo := (9272901 / 500000000)) (hi := (18545803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245406278271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245406278271) = 1/(245406278271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18545803 / 1000000000) (-9272901 / 500000000) (Real.log (245406278271 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (576927 / 31250000) ≤ -Real.log (981707707999 / 1000000000000) ∧
    -Real.log (981707707999 / 1000000000000) ≤ (3692333 / 200000000) := by
  have h := checkLog_sound (w := (18292292001 / 1981707707999)) (n := 12)
    (lo := (576927 / 31250000)) (hi := (3692333 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981707707999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981707707999) = 1/(981707707999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3692333 / 200000000) (-576927 / 31250000) (Real.log (981707707999 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell029
