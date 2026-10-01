import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0073
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

theorem reflection_log_1_neg : (355815199 / 1000000000) ≤ -Real.log (1280 / 1827) ∧
    -Real.log (1280 / 1827) ≤ (444769 / 1250000) := by
  have h := checkLog_sound (w := (547 / 3107)) (n := 12)
    (lo := (355815199 / 1000000000)) (hi := (444769 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1827 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1827 / 1280) = 1/(1280 / 1827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (355815199 / 1000000000) (444769 / 1250000) (Real.log (1827 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1827 / 1280) = -Real.log (1280 / 1827) := by
    rw [show ((1827 / 1280) : ℝ) = ((1280 / 1827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (111493931 / 200000000) ≤ -Real.log (733 / 1280) ∧
    -Real.log (733 / 1280) ≤ (69683707 / 125000000) := by
  have h := checkLog_sound (w := (547 / 2013)) (n := 12)
    (lo := (111493931 / 200000000)) (hi := (69683707 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 733) = 1/(733 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-69683707 / 125000000) (-111493931 / 200000000) (Real.log (733 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (88748461 / 250000000) ≤ -Real.log (2560 / 3651) ∧
    -Real.log (2560 / 3651) ≤ (70998769 / 200000000) := by
  have h := checkLog_sound (w := (1091 / 6211)) (n := 12)
    (lo := (88748461 / 250000000)) (hi := (70998769 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3651 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3651 / 2560) = 1/(2560 / 3651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (88748461 / 250000000) (70998769 / 200000000) (Real.log (3651 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3651 / 2560) = -Real.log (2560 / 3651) := by
    rw [show ((3651 / 2560) : ℝ) = ((2560 / 3651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (555425361 / 1000000000) ≤ -Real.log (1469 / 2560) ∧
    -Real.log (1469 / 2560) ≤ (277712681 / 500000000) := by
  have h := checkLog_sound (w := (1091 / 4029)) (n := 12)
    (lo := (555425361 / 1000000000)) (hi := (277712681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1469) = 1/(1469 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-277712681 / 500000000) (-555425361 / 1000000000) (Real.log (1469 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (308858109 / 500000000) ≤ -Real.log (640 / 1187) ∧
    -Real.log (640 / 1187) ≤ (617716219 / 1000000000) := by
  have h := checkLog_sound (w := (547 / 1827)) (n := 12)
    (lo := (308858109 / 500000000)) (hi := (617716219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187 / 640) = 1/(640 / 1187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (308858109 / 500000000) (617716219 / 1000000000) (Real.log (1187 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1187 / 640) = -Real.log (640 / 1187) := by
    rw [show ((1187 / 640) : ℝ) = ((640 / 1187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (964434341 / 500000000) ≤ -Real.log (93 / 640) ∧
    -Real.log (93 / 640) ≤ (385773737 / 200000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 93) = 1/(93 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-385773737 / 200000000) (-964434341 / 500000000) (Real.log (93 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (616451729 / 1000000000) ≤ -Real.log (1280 / 2371) ∧
    -Real.log (1280 / 2371) ≤ (61645173 / 100000000) := by
  have h := checkLog_sound (w := (1091 / 3651)) (n := 12)
    (lo := (616451729 / 1000000000)) (hi := (61645173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2371 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2371 / 1280) = 1/(1280 / 2371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (616451729 / 1000000000) (61645173 / 100000000) (Real.log (2371 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2371 / 1280) = -Real.log (1280 / 2371) := by
    rw [show ((2371 / 1280) : ℝ) = ((1280 / 2371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (95643417 / 50000000) ≤ -Real.log (189 / 1280) ∧
    -Real.log (189 / 1280) ≤ (1912868343 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 189) = 1/(189 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1912868343 / 1000000000) (-95643417 / 50000000) (Real.log (189 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (489077437 / 1000000000) ≤ -Real.log (1000000 / 1630811) ∧
    -Real.log (1000000 / 1630811) ≤ (244538719 / 500000000) := by
  have h := checkLog_sound (w := (630811 / 2630811)) (n := 12)
    (lo := (489077437 / 1000000000)) (hi := (244538719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1630811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1630811 / 1000000) = 1/(1000000 / 1630811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (489077437 / 1000000000) (244538719 / 500000000) (Real.log (1630811 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1630811 / 1000000) = -Real.log (1000000 / 1630811) := by
    rw [show ((1630811 / 1000000) : ℝ) = ((1000000 / 1630811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (99644657 / 100000000) ≤ -Real.log (369189 / 1000000) ∧
    -Real.log (369189 / 1000000) ≤ (249111643 / 250000000) := by
  have h := checkLog_sound (w := (130811 / 869189)) (n := 12)
    (lo := (30329939 / 100000000)) (hi := (303299391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 369189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 369189) = 1/(369189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-249111643 / 250000000) (-99644657 / 100000000) (Real.log (369189 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (61287807 / 125000000) ≤ -Real.log (100000 / 163281) ∧
    -Real.log (100000 / 163281) ≤ (490302457 / 1000000000) := by
  have h := checkLog_sound (w := (63281 / 263281)) (n := 12)
    (lo := (61287807 / 125000000)) (hi := (490302457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163281 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163281 / 100000) = 1/(100000 / 163281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (61287807 / 125000000) (490302457 / 1000000000) (Real.log (163281 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (163281 / 100000) = -Real.log (100000 / 163281) := by
    rw [show ((163281 / 100000) : ℝ) = ((100000 / 163281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1001875853 / 1000000000) ≤ -Real.log (36719 / 100000) ∧
    -Real.log (36719 / 100000) ≤ (200375171 / 200000000) := by
  have h := checkLog_sound (w := (13281 / 86719)) (n := 12)
    (lo := (308728673 / 1000000000)) (hi := (154364337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36719) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 36719) = 1/(36719 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-200375171 / 200000000) (-1001875853 / 1000000000) (Real.log (36719 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (81187799 / 200000000) ≤ -Real.log (1000000 / 1500711) ∧
    -Real.log (1000000 / 1500711) ≤ (101484749 / 250000000) := by
  have h := checkLog_sound (w := (500711 / 2500711)) (n := 12)
    (lo := (81187799 / 200000000)) (hi := (101484749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1500711 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1500711 / 1000000) = 1/(1000000 / 1500711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (81187799 / 200000000) (101484749 / 250000000) (Real.log (1500711 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1500711 / 1000000) = -Real.log (1000000 / 1500711) := by
    rw [show ((1500711 / 1000000) : ℝ) = ((1000000 / 1500711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (43410637 / 62500000) ≤ -Real.log (499289 / 1000000) ∧
    -Real.log (499289 / 1000000) ≤ (347285097 / 500000000) := by
  have h := checkLog_sound (w := (711 / 999289)) (n := 12)
    (lo := (355753 / 250000000)) (hi := (1423013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499289) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 499289) = 1/(499289 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-347285097 / 500000000) (-43410637 / 62500000) (Real.log (499289 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (203625423 / 500000000) ≤ -Real.log (1000000 / 1502681) ∧
    -Real.log (1000000 / 1502681) ≤ (407250847 / 1000000000) := by
  have h := checkLog_sound (w := (502681 / 2502681)) (n := 12)
    (lo := (203625423 / 500000000)) (hi := (407250847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1502681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1502681 / 1000000) = 1/(1000000 / 1502681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (203625423 / 500000000) (407250847 / 1000000000) (Real.log (1502681 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1502681 / 1000000) = -Real.log (1000000 / 1502681) := by
    rw [show ((1502681 / 1000000) : ℝ) = ((1000000 / 1502681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (698523607 / 1000000000) ≤ -Real.log (497319 / 1000000) ∧
    -Real.log (497319 / 1000000) ≤ (698523609 / 1000000000) := by
  have h := checkLog_sound (w := (2681 / 997319)) (n := 12)
    (lo := (5376427 / 1000000000)) (hi := (1344107 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 497319) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 497319) = 1/(497319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-698523609 / 1000000000) (-698523607 / 1000000000) (Real.log (497319 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (742762003 / 500000000) ≤ -Real.log (125000000000 / 552159937051) ∧
    -Real.log (125000000000 / 552159937051) ≤ (1485524009 / 1000000000) := by
  have h := checkLog_sound (w := (52159937051 / 1052159937051)) (n := 12)
    (lo := (49614823 / 500000000)) (hi := (99229647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((552159937051 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(552159937051 / 500000000000) = 1/(125000000000 / 552159937051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (742762003 / 500000000) (1485524009 / 1000000000) (Real.log (552159937051 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (552159937051 / 125000000000) = -Real.log (125000000000 / 552159937051) := by
    rw [show ((552159937051 / 125000000000) : ℝ) = ((125000000000 / 552159937051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1492178309 / 1000000000) ≤ -Real.log (500000000000 / 2223385713119) ∧
    -Real.log (500000000000 / 2223385713119) ≤ (186522289 / 125000000) := by
  have h := checkLog_sound (w := (223385713119 / 4223385713119)) (n := 12)
    (lo := (105883949 / 1000000000)) (hi := (2117679 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2223385713119 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2223385713119 / 2000000000000) = 1/(500000000000 / 2223385713119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1492178309 / 1000000000) (186522289 / 125000000) (Real.log (2223385713119 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2223385713119 / 500000000000) = -Real.log (500000000000 / 2223385713119) := by
    rw [show ((2223385713119 / 500000000000) : ℝ) = ((500000000000 / 2223385713119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1100509187 / 1000000000) ≤ -Real.log (250000000000 / 751424024963) ∧
    -Real.log (250000000000 / 751424024963) ≤ (1100509189 / 1000000000) := by
  have h := checkLog_sound (w := (251424024963 / 1251424024963)) (n := 12)
    (lo := (407362007 / 1000000000)) (hi := (50920251 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751424024963 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(751424024963 / 500000000000) = 1/(250000000000 / 751424024963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1100509187 / 1000000000) (1100509189 / 1000000000) (Real.log (751424024963 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (751424024963 / 250000000000) = -Real.log (250000000000 / 751424024963) := by
    rw [show ((751424024963 / 250000000000) : ℝ) = ((250000000000 / 751424024963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1105774453 / 1000000000) ≤ -Real.log (500000000000 / 1510781812077) ∧
    -Real.log (500000000000 / 1510781812077) ≤ (221154891 / 200000000) := by
  have h := checkLog_sound (w := (510781812077 / 2510781812077)) (n := 12)
    (lo := (412627273 / 1000000000)) (hi := (206313637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1510781812077 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1510781812077 / 1000000000000) = 1/(500000000000 / 1510781812077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1105774453 / 1000000000) (221154891 / 200000000) (Real.log (1510781812077 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1510781812077 / 500000000000) = -Real.log (500000000000 / 1510781812077) := by
    rw [show ((1510781812077 / 500000000000) : ℝ) = ((500000000000 / 1510781812077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0073
