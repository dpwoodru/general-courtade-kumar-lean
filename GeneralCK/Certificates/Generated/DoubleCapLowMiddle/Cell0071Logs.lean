import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0071
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

theorem reflection_log_1_neg : (676892743 / 1000000000) ≤ -Real.log (51200 / 100749) ∧
    -Real.log (51200 / 100749) ≤ (84611593 / 125000000) := by
  have h := checkLog_sound (w := (49549 / 151949)) (n := 12)
    (lo := (676892743 / 1000000000)) (hi := (84611593 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100749 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100749 / 51200) = 1/(51200 / 100749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (676892743 / 1000000000) (84611593 / 125000000) (Real.log (100749 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100749 / 51200) = -Real.log (51200 / 100749) := by
    rw [show ((100749 / 51200) : ℝ) = ((51200 / 100749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (858589591 / 250000000) ≤ -Real.log (1651 / 51200) ∧
    -Real.log (1651 / 51200) ≤ (3434358369 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 4851)) (n := 12)
    (lo := (165442411 / 250000000)) (hi := (132353929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1651) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1651) = 1/(1651 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3434358369 / 1000000000) (-858589591 / 250000000) (Real.log (1651 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (676704137 / 1000000000) ≤ -Real.log (5120 / 10073) ∧
    -Real.log (5120 / 10073) ≤ (338352069 / 500000000) := by
  have h := checkLog_sound (w := (4953 / 15193)) (n := 12)
    (lo := (676704137 / 1000000000)) (hi := (338352069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10073 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10073 / 5120) = 1/(5120 / 10073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (676704137 / 1000000000) (338352069 / 500000000) (Real.log (10073 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (10073 / 5120) = -Real.log (5120 / 10073) := by
    rw [show ((10073 / 5120) : ℝ) = ((5120 / 10073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3422915903 / 1000000000) ≤ -Real.log (167 / 5120) ∧
    -Real.log (167 / 5120) ≤ (855728977 / 250000000) := by
  have h := checkLog_sound (w := (153 / 487)) (n := 12)
    (lo := (650327183 / 1000000000)) (hi := (40645449 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 167) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 167) = 1/(167 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-855728977 / 250000000) (-3422915903 / 1000000000) (Real.log (167 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (660369727 / 1000000000) ≤ -Real.log (25600 / 49549) ∧
    -Real.log (25600 / 49549) ≤ (10318277 / 15625000) := by
  have h := checkLog_sound (w := (23949 / 75149)) (n := 12)
    (lo := (660369727 / 1000000000)) (hi := (10318277 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49549 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49549 / 25600) = 1/(25600 / 49549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (660369727 / 1000000000) (10318277 / 15625000) (Real.log (49549 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49549 / 25600) = -Real.log (25600 / 49549) := by
    rw [show ((49549 / 25600) : ℝ) = ((25600 / 49549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (171325699 / 62500000) ≤ -Real.log (1651 / 25600) ∧
    -Real.log (1651 / 25600) ≤ (685302797 / 250000000) := by
  have h := checkLog_sound (w := (1549 / 4851)) (n := 12)
    (lo := (165442411 / 250000000)) (hi := (132353929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1651) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1651) = 1/(1651 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-685302797 / 250000000) (-171325699 / 62500000) (Real.log (1651 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (131997239 / 200000000) ≤ -Real.log (2560 / 4953) ∧
    -Real.log (2560 / 4953) ≤ (164996549 / 250000000) := by
  have h := checkLog_sound (w := (2393 / 7513)) (n := 12)
    (lo := (131997239 / 200000000)) (hi := (164996549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4953 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4953 / 2560) = 1/(2560 / 4953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (131997239 / 200000000) (164996549 / 250000000) (Real.log (4953 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4953 / 2560) = -Real.log (2560 / 4953) := by
    rw [show ((4953 / 2560) : ℝ) = ((2560 / 4953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2729768723 / 1000000000) ≤ -Real.log (167 / 2560) ∧
    -Real.log (167 / 2560) ≤ (2729768727 / 1000000000) := by
  have h := checkLog_sound (w := (153 / 487)) (n := 12)
    (lo := (650327183 / 1000000000)) (hi := (40645449 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 167) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 167) = 1/(167 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2729768727 / 1000000000) (-2729768723 / 1000000000) (Real.log (167 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (679475649 / 1000000000) ≤ -Real.log (1000000 / 1972843) ∧
    -Real.log (1000000 / 1972843) ≤ (13589513 / 20000000) := by
  have h := checkLog_sound (w := (972843 / 2972843)) (n := 12)
    (lo := (679475649 / 1000000000)) (hi := (13589513 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1972843 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1972843 / 1000000) = 1/(1000000 / 1972843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (679475649 / 1000000000) (13589513 / 20000000) (Real.log (1972843 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1972843 / 1000000) = -Real.log (1000000 / 1972843) := by
    rw [show ((1972843 / 1000000) : ℝ) = ((1000000 / 1972843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (901530109 / 250000000) ≤ -Real.log (27157 / 1000000) ∧
    -Real.log (27157 / 1000000) ≤ (1803060221 / 500000000) := by
  have h := checkLog_sound (w := (4093 / 58407)) (n := 12)
    (lo := (17548067 / 125000000)) (hi := (140384537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27157) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 27157) = 1/(27157 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1803060221 / 500000000) (-901530109 / 250000000) (Real.log (27157 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42476573 / 62500000) ≤ -Real.log (500000 / 986569) ∧
    -Real.log (500000 / 986569) ≤ (679625169 / 1000000000) := by
  have h := checkLog_sound (w := (486569 / 1486569)) (n := 12)
    (lo := (42476573 / 62500000)) (hi := (679625169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986569 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986569 / 500000) = 1/(500000 / 986569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42476573 / 62500000) (679625169 / 1000000000) (Real.log (986569 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (986569 / 500000) = -Real.log (500000 / 986569) := by
    rw [show ((986569 / 500000) : ℝ) = ((500000 / 986569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3617042627 / 1000000000) ≤ -Real.log (13431 / 500000) ∧
    -Real.log (13431 / 500000) ≤ (3617042633 / 1000000000) := by
  have h := checkLog_sound (w := (1097 / 14528)) (n := 12)
    (lo := (151306727 / 1000000000)) (hi := (18913341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13431) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13431) = 1/(13431 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3617042633 / 1000000000) (-3617042627 / 1000000000) (Real.log (13431 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (135876577 / 200000000) ≤ -Real.log (50000 / 98633) ∧
    -Real.log (50000 / 98633) ≤ (339691443 / 500000000) := by
  have h := checkLog_sound (w := (48633 / 148633)) (n := 12)
    (lo := (135876577 / 200000000)) (hi := (339691443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98633 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98633 / 50000) = 1/(50000 / 98633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (135876577 / 200000000) (339691443 / 500000000) (Real.log (98633 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (98633 / 50000) = -Real.log (50000 / 98633) := by
    rw [show ((98633 / 50000) : ℝ) = ((50000 / 98633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (899851111 / 250000000) ≤ -Real.log (1367 / 50000) ∧
    -Real.log (1367 / 50000) ≤ (71988089 / 20000000) := by
  have h := checkLog_sound (w := (391 / 5859)) (n := 12)
    (lo := (2088571 / 15625000)) (hi := (26733709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2734) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2734) = 1/(1367 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-71988089 / 20000000) (-899851111 / 250000000) (Real.log (1367 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (339767223 / 500000000) ≤ -Real.log (1000000 / 1972959) ∧
    -Real.log (1000000 / 1972959) ≤ (679534447 / 1000000000) := by
  have h := checkLog_sound (w := (972959 / 2972959)) (n := 12)
    (lo := (339767223 / 500000000)) (hi := (679534447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1972959 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1972959 / 1000000) = 1/(1000000 / 1972959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (339767223 / 500000000) (679534447 / 1000000000) (Real.log (1972959 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1972959 / 1000000) = -Real.log (1000000 / 1972959) := by
    rw [show ((1972959 / 1000000) : ℝ) = ((1000000 / 1972959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3610401043 / 1000000000) ≤ -Real.log (27041 / 1000000) ∧
    -Real.log (27041 / 1000000) ≤ (3610401049 / 1000000000) := by
  have h := checkLog_sound (w := (4209 / 58291)) (n := 12)
    (lo := (144665143 / 1000000000)) (hi := (18083143 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27041) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 27041) = 1/(27041 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3610401049 / 1000000000) (-3610401043 / 1000000000) (Real.log (27041 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (857119217 / 200000000) ≤ -Real.log (500000000000 / 36322918584527) ∧
    -Real.log (500000000000 / 36322918584527) ≤ (1071399023 / 250000000) := by
  have h := checkLog_sound (w := (4322918584527 / 68322918584527)) (n := 12)
    (lo := (25342601 / 200000000)) (hi := (63356503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36322918584527 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(36322918584527 / 32000000000000) = 1/(500000000000 / 36322918584527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (857119217 / 200000000) (1071399023 / 250000000) (Real.log (36322918584527 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (36322918584527 / 500000000000) = -Real.log (500000000000 / 36322918584527) := by
    rw [show ((36322918584527 / 500000000000) : ℝ) = ((500000000000 / 36322918584527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (859333559 / 200000000) ≤ -Real.log (500000000000 / 36727309954583) ∧
    -Real.log (500000000000 / 36727309954583) ≤ (2148333901 / 500000000) := by
  have h := checkLog_sound (w := (4727309954583 / 68727309954583)) (n := 12)
    (lo := (27556943 / 200000000)) (hi := (34446179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36727309954583 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(36727309954583 / 32000000000000) = 1/(500000000000 / 36727309954583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (859333559 / 200000000) (2148333901 / 500000000) (Real.log (36727309954583 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (36727309954583 / 500000000000) = -Real.log (500000000000 / 36727309954583) := by
    rw [show ((36727309954583 / 500000000000) : ℝ) = ((500000000000 / 36727309954583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (427878733 / 100000000) ≤ -Real.log (15625000000 / 1127388899049) ∧
    -Real.log (15625000000 / 1127388899049) ≤ (4278787337 / 1000000000) := by
  have h := checkLog_sound (w := (127388899049 / 2127388899049)) (n := 12)
    (lo := (479617 / 4000000)) (hi := (119904251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127388899049 / 1000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1127388899049 / 1000000000000) = 1/(15625000000 / 1127388899049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (427878733 / 100000000) (4278787337 / 1000000000) (Real.log (1127388899049 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1127388899049 / 15625000000) = -Real.log (15625000000 / 1127388899049) := by
    rw [show ((1127388899049 / 15625000000) : ℝ) = ((15625000000 / 1127388899049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4289935489 / 1000000000) ≤ -Real.log (500000000000 / 36480880884583) ∧
    -Real.log (500000000000 / 36480880884583) ≤ (536241937 / 125000000) := by
  have h := checkLog_sound (w := (4480880884583 / 68480880884583)) (n := 12)
    (lo := (131052409 / 1000000000)) (hi := (13105241 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36480880884583 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(36480880884583 / 32000000000000) = 1/(500000000000 / 36480880884583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4289935489 / 1000000000) (536241937 / 125000000) (Real.log (36480880884583 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (36480880884583 / 500000000000) = -Real.log (500000000000 / 36480880884583) := by
    rw [show ((36480880884583 / 500000000000) : ℝ) = ((500000000000 / 36480880884583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0071
