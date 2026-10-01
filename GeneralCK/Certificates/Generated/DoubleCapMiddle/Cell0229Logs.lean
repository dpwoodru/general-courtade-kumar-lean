import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0229
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

theorem reflection_log_1_neg : (252550643 / 1000000000) ≤ -Real.log (5120 / 6591) ∧
    -Real.log (5120 / 6591) ≤ (63137661 / 250000000) := by
  have h := checkLog_sound (w := (1471 / 11711)) (n := 12)
    (lo := (252550643 / 1000000000)) (hi := (63137661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6591 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6591 / 5120) = 1/(5120 / 6591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (252550643 / 1000000000) (63137661 / 250000000) (Real.log (6591 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6591 / 5120) = -Real.log (5120 / 6591) := by
    rw [show ((6591 / 5120) : ℝ) = ((5120 / 6591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (338701281 / 1000000000) ≤ -Real.log (3649 / 5120) ∧
    -Real.log (3649 / 5120) ≤ (169350641 / 500000000) := by
  have h := checkLog_sound (w := (1471 / 8769)) (n := 12)
    (lo := (338701281 / 1000000000)) (hi := (169350641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3649) = 1/(3649 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-169350641 / 500000000) (-338701281 / 1000000000) (Real.log (3649 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (252095373 / 1000000000) ≤ -Real.log (1280 / 1647) ∧
    -Real.log (1280 / 1647) ≤ (126047687 / 500000000) := by
  have h := checkLog_sound (w := (367 / 2927)) (n := 12)
    (lo := (252095373 / 1000000000)) (hi := (126047687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1647 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1647 / 1280) = 1/(1280 / 1647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (252095373 / 1000000000) (126047687 / 500000000) (Real.log (1647 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1647 / 1280) = -Real.log (1280 / 1647) := by
    rw [show ((1647 / 1280) : ℝ) = ((1280 / 1647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (84469869 / 250000000) ≤ -Real.log (913 / 1280) ∧
    -Real.log (913 / 1280) ≤ (337879477 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 2193)) (n := 12)
    (lo := (84469869 / 250000000)) (hi := (337879477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 913) = 1/(913 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-337879477 / 1000000000) (-84469869 / 250000000) (Real.log (913 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (18160289 / 40000000) ≤ -Real.log (2560 / 4031) ∧
    -Real.log (2560 / 4031) ≤ (227003613 / 500000000) := by
  have h := checkLog_sound (w := (1471 / 6591)) (n := 12)
    (lo := (18160289 / 40000000)) (hi := (227003613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4031 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4031 / 2560) = 1/(2560 / 4031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (18160289 / 40000000) (227003613 / 500000000) (Real.log (4031 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4031 / 2560) = -Real.log (2560 / 4031) := by
    rw [show ((4031 / 2560) : ℝ) = ((2560 / 4031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (854747413 / 1000000000) ≤ -Real.log (1089 / 2560) ∧
    -Real.log (1089 / 2560) ≤ (170949483 / 200000000) := by
  have h := checkLog_sound (w := (191 / 2369)) (n := 12)
    (lo := (161600233 / 1000000000)) (hi := (80800117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1089) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1089) = 1/(1089 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-170949483 / 200000000) (-854747413 / 1000000000) (Real.log (1089 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (113315679 / 250000000) ≤ -Real.log (640 / 1007) ∧
    -Real.log (640 / 1007) ≤ (453262717 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 1647)) (n := 12)
    (lo := (113315679 / 250000000)) (hi := (453262717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1007 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1007 / 640) = 1/(640 / 1007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (113315679 / 250000000) (453262717 / 1000000000) (Real.log (1007 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1007 / 640) = -Real.log (640 / 1007) := by
    rw [show ((1007 / 640) : ℝ) = ((640 / 1007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (42599819 / 50000000) ≤ -Real.log (273 / 640) ∧
    -Real.log (273 / 640) ≤ (425998191 / 500000000) := by
  have h := checkLog_sound (w := (47 / 593)) (n := 12)
    (lo := (397123 / 2500000)) (hi := (158849201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 273) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 273) = 1/(273 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-425998191 / 500000000) (-42599819 / 50000000) (Real.log (273 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (344982351 / 1000000000) ≤ -Real.log (200000 / 282393) ∧
    -Real.log (200000 / 282393) ≤ (21561397 / 62500000) := by
  have h := checkLog_sound (w := (82393 / 482393)) (n := 12)
    (lo := (344982351 / 1000000000)) (hi := (21561397 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((282393 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(282393 / 200000) = 1/(200000 / 282393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (344982351 / 1000000000) (21561397 / 62500000) (Real.log (282393 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (282393 / 200000) = -Real.log (200000 / 282393) := by
    rw [show ((282393 / 200000) : ℝ) = ((200000 / 282393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (530968809 / 1000000000) ≤ -Real.log (117607 / 200000) ∧
    -Real.log (117607 / 200000) ≤ (53096881 / 100000000) := by
  have h := checkLog_sound (w := (82393 / 317607)) (n := 12)
    (lo := (530968809 / 1000000000)) (hi := (53096881 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 117607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 117607) = 1/(117607 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-53096881 / 100000000) (-530968809 / 1000000000) (Real.log (117607 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (69120231 / 200000000) ≤ -Real.log (1000000 / 1412839) ∧
    -Real.log (1000000 / 1412839) ≤ (86400289 / 250000000) := by
  have h := checkLog_sound (w := (412839 / 2412839)) (n := 12)
    (lo := (69120231 / 200000000)) (hi := (86400289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1412839 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1412839 / 1000000) = 1/(1000000 / 1412839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (69120231 / 200000000) (86400289 / 250000000) (Real.log (1412839 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1412839 / 1000000) = -Real.log (1000000 / 1412839) := by
    rw [show ((1412839 / 1000000) : ℝ) = ((1000000 / 1412839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (26622811 / 50000000) ≤ -Real.log (587161 / 1000000) ∧
    -Real.log (587161 / 1000000) ≤ (532456221 / 1000000000) := by
  have h := checkLog_sound (w := (412839 / 1587161)) (n := 12)
    (lo := (26622811 / 50000000)) (hi := (532456221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 587161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 587161) = 1/(587161 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-532456221 / 1000000000) (-26622811 / 50000000) (Real.log (587161 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (133346671 / 500000000) ≤ -Real.log (25000 / 32641) ∧
    -Real.log (25000 / 32641) ≤ (266693343 / 1000000000) := by
  have h := checkLog_sound (w := (7641 / 57641)) (n := 12)
    (lo := (133346671 / 500000000)) (hi := (266693343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32641 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32641 / 25000) = 1/(25000 / 32641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (133346671 / 500000000) (266693343 / 1000000000) (Real.log (32641 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (32641 / 25000) = -Real.log (25000 / 32641) := by
    rw [show ((32641 / 25000) : ℝ) = ((25000 / 32641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4559559 / 12500000) ≤ -Real.log (17359 / 25000) ∧
    -Real.log (17359 / 25000) ≤ (364764721 / 1000000000) := by
  have h := checkLog_sound (w := (7641 / 42359)) (n := 12)
    (lo := (4559559 / 12500000)) (hi := (364764721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 17359) = 1/(17359 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-364764721 / 1000000000) (-4559559 / 12500000) (Real.log (17359 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (53447857 / 200000000) ≤ -Real.log (1000000 / 1306353) ∧
    -Real.log (1000000 / 1306353) ≤ (133619643 / 500000000) := by
  have h := checkLog_sound (w := (306353 / 2306353)) (n := 12)
    (lo := (53447857 / 200000000)) (hi := (133619643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1306353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1306353 / 1000000) = 1/(1000000 / 1306353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (53447857 / 200000000) (133619643 / 500000000) (Real.log (1306353 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1306353 / 1000000) = -Real.log (1000000 / 1306353) := by
    rw [show ((1306353 / 1000000) : ℝ) = ((1000000 / 1306353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (365792093 / 1000000000) ≤ -Real.log (693647 / 1000000) ∧
    -Real.log (693647 / 1000000) ≤ (182896047 / 500000000) := by
  have h := checkLog_sound (w := (306353 / 1693647)) (n := 12)
    (lo := (365792093 / 1000000000)) (hi := (182896047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 693647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 693647) = 1/(693647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-182896047 / 500000000) (-365792093 / 1000000000) (Real.log (693647 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (875951159 / 1000000000) ≤ -Real.log (100000000000 / 240115809433) ∧
    -Real.log (100000000000 / 240115809433) ≤ (875951161 / 1000000000) := by
  have h := checkLog_sound (w := (40115809433 / 440115809433)) (n := 12)
    (lo := (182803979 / 1000000000)) (hi := (9140199 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((240115809433 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(240115809433 / 200000000000) = 1/(100000000000 / 240115809433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (875951159 / 1000000000) (875951161 / 1000000000) (Real.log (240115809433 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (240115809433 / 100000000000) = -Real.log (100000000000 / 240115809433) := by
    rw [show ((240115809433 / 100000000000) : ℝ) = ((100000000000 / 240115809433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (7024459 / 8000000) ≤ -Real.log (500000000000 / 1203110390507) ∧
    -Real.log (500000000000 / 1203110390507) ≤ (878057377 / 1000000000) := by
  have h := checkLog_sound (w := (203110390507 / 2203110390507)) (n := 12)
    (lo := (36982039 / 200000000)) (hi := (46227549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203110390507 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1203110390507 / 1000000000000) = 1/(500000000000 / 1203110390507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (7024459 / 8000000) (878057377 / 1000000000) (Real.log (1203110390507 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1203110390507 / 500000000000) = -Real.log (500000000000 / 1203110390507) := by
    rw [show ((1203110390507 / 500000000000) : ℝ) = ((500000000000 / 1203110390507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (315729031 / 500000000) ≤ -Real.log (100000000000 / 188035025059) ∧
    -Real.log (100000000000 / 188035025059) ≤ (631458063 / 1000000000) := by
  have h := checkLog_sound (w := (88035025059 / 288035025059)) (n := 12)
    (lo := (315729031 / 500000000)) (hi := (631458063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188035025059 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188035025059 / 100000000000) = 1/(100000000000 / 188035025059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (315729031 / 500000000) (631458063 / 1000000000) (Real.log (188035025059 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (188035025059 / 100000000000) = -Real.log (100000000000 / 188035025059) := by
    rw [show ((188035025059 / 100000000000) : ℝ) = ((100000000000 / 188035025059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (316515689 / 500000000) ≤ -Real.log (500000000000 / 941655481823) ∧
    -Real.log (500000000000 / 941655481823) ≤ (633031379 / 1000000000) := by
  have h := checkLog_sound (w := (441655481823 / 1441655481823)) (n := 12)
    (lo := (316515689 / 500000000)) (hi := (633031379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941655481823 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941655481823 / 500000000000) = 1/(500000000000 / 941655481823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (316515689 / 500000000) (633031379 / 1000000000) (Real.log (941655481823 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (941655481823 / 500000000000) = -Real.log (500000000000 / 941655481823) := by
    rw [show ((941655481823 / 500000000000) : ℝ) = ((500000000000 / 941655481823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0229
