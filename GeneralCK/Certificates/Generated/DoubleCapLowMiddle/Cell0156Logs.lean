import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0156
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

theorem reflection_log_1_neg : (324389433 / 500000000) ≤ -Real.log (12800 / 24489) ∧
    -Real.log (12800 / 24489) ≤ (648778867 / 1000000000) := by
  have h := checkLog_sound (w := (11689 / 37289)) (n := 12)
    (lo := (324389433 / 500000000)) (hi := (648778867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24489 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24489 / 12800) = 1/(12800 / 24489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (324389433 / 500000000) (648778867 / 1000000000) (Real.log (24489 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24489 / 12800) = -Real.log (12800 / 24489) := by
    rw [show ((24489 / 12800) : ℝ) = ((12800 / 24489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1222092329 / 500000000) ≤ -Real.log (1111 / 12800) ∧
    -Real.log (1111 / 12800) ≤ (1222092331 / 500000000) := by
  have h := checkLog_sound (w := (489 / 2711)) (n := 12)
    (lo := (182371559 / 500000000)) (hi := (364743119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1111) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1111) = 1/(1111 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1222092331 / 500000000) (-1222092329 / 500000000) (Real.log (1111 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (324001353 / 500000000) ≤ -Real.log (1280 / 2447) ∧
    -Real.log (1280 / 2447) ≤ (648002707 / 1000000000) := by
  have h := checkLog_sound (w := (1167 / 3727)) (n := 12)
    (lo := (324001353 / 500000000)) (hi := (648002707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2447 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2447 / 1280) = 1/(1280 / 2447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (324001353 / 500000000) (648002707 / 1000000000) (Real.log (2447 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2447 / 1280) = -Real.log (1280 / 2447) := by
    rw [show ((2447 / 1280) : ℝ) = ((1280 / 2447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (151701721 / 62500000) ≤ -Real.log (113 / 1280) ∧
    -Real.log (113 / 1280) ≤ (121361377 / 50000000) := by
  have h := checkLog_sound (w := (47 / 273)) (n := 12)
    (lo := (86946499 / 250000000)) (hi := (347785997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 113) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 113) = 1/(113 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-121361377 / 50000000) (-151701721 / 62500000) (Real.log (113 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (301175119 / 500000000) ≤ -Real.log (6400 / 11689) ∧
    -Real.log (6400 / 11689) ≤ (602350239 / 1000000000) := by
  have h := checkLog_sound (w := (5289 / 18089)) (n := 12)
    (lo := (301175119 / 500000000)) (hi := (602350239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11689 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11689 / 6400) = 1/(6400 / 11689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (301175119 / 500000000) (602350239 / 1000000000) (Real.log (11689 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11689 / 6400) = -Real.log (6400 / 11689) := by
    rw [show ((11689 / 6400) : ℝ) = ((6400 / 11689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (875518739 / 500000000) ≤ -Real.log (1111 / 6400) ∧
    -Real.log (1111 / 6400) ≤ (1751037481 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 2711)) (n := 12)
    (lo := (182371559 / 500000000)) (hi := (364743119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1111) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1111) = 1/(1111 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1751037481 / 1000000000) (-875518739 / 500000000) (Real.log (1111 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (120144691 / 200000000) ≤ -Real.log (640 / 1167) ∧
    -Real.log (640 / 1167) ≤ (1173288 / 1953125) := by
  have h := checkLog_sound (w := (527 / 1807)) (n := 12)
    (lo := (120144691 / 200000000)) (hi := (1173288 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1167 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1167 / 640) = 1/(640 / 1167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (120144691 / 200000000) (1173288 / 1953125) (Real.log (1167 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1167 / 640) = -Real.log (640 / 1167) := by
    rw [show ((1167 / 640) : ℝ) = ((640 / 1167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (433520089 / 250000000) ≤ -Real.log (113 / 640) ∧
    -Real.log (113 / 640) ≤ (1734080359 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 273)) (n := 12)
    (lo := (86946499 / 250000000)) (hi := (347785997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 113) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 113) = 1/(113 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1734080359 / 1000000000) (-433520089 / 250000000) (Real.log (113 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (131656067 / 200000000) ≤ -Real.log (250000 / 482867) ∧
    -Real.log (250000 / 482867) ≤ (41142521 / 62500000) := by
  have h := checkLog_sound (w := (232867 / 732867)) (n := 12)
    (lo := (131656067 / 200000000)) (hi := (41142521 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((482867 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(482867 / 250000) = 1/(250000 / 482867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (131656067 / 200000000) (41142521 / 62500000) (Real.log (482867 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (482867 / 250000) = -Real.log (250000 / 482867) := by
    rw [show ((482867 / 250000) : ℝ) = ((250000 / 482867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2680454487 / 1000000000) ≤ -Real.log (17133 / 250000) ∧
    -Real.log (17133 / 250000) ≤ (2680454491 / 1000000000) := by
  have h := checkLog_sound (w := (14117 / 48383)) (n := 12)
    (lo := (601012947 / 1000000000)) (hi := (150253237 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17133) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 17133) = 1/(17133 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2680454491 / 1000000000) (-2680454487 / 1000000000) (Real.log (17133 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (658818641 / 1000000000) ≤ -Real.log (250000 / 483127) ∧
    -Real.log (250000 / 483127) ≤ (329409321 / 500000000) := by
  have h := checkLog_sound (w := (233127 / 733127)) (n := 12)
    (lo := (658818641 / 1000000000)) (hi := (329409321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483127 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483127 / 250000) = 1/(250000 / 483127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (658818641 / 1000000000) (329409321 / 500000000) (Real.log (483127 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (483127 / 250000) = -Real.log (250000 / 483127) := by
    rw [show ((483127 / 250000) : ℝ) = ((250000 / 483127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (673936551 / 250000000) ≤ -Real.log (16873 / 250000) ∧
    -Real.log (16873 / 250000) ≤ (84242069 / 31250000) := by
  have h := checkLog_sound (w := (14377 / 48123)) (n := 12)
    (lo := (77038083 / 125000000)) (hi := (123260933 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16873) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 16873) = 1/(16873 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-84242069 / 31250000) (-673936551 / 250000000) (Real.log (16873 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (131472599 / 200000000) ≤ -Real.log (1000000 / 1929697) ∧
    -Real.log (1000000 / 1929697) ≤ (164340749 / 250000000) := by
  have h := checkLog_sound (w := (929697 / 2929697)) (n := 12)
    (lo := (131472599 / 200000000)) (hi := (164340749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1929697 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1929697 / 1000000) = 1/(1000000 / 1929697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (131472599 / 200000000) (164340749 / 250000000) (Real.log (1929697 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1929697 / 1000000) = -Real.log (1000000 / 1929697) := by
    rw [show ((1929697 / 1000000) : ℝ) = ((1000000 / 1929697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (530988161 / 200000000) ≤ -Real.log (70303 / 1000000) ∧
    -Real.log (70303 / 1000000) ≤ (2654940809 / 1000000000) := by
  have h := checkLog_sound (w := (54697 / 195303)) (n := 12)
    (lo := (115099853 / 200000000)) (hi := (287749633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 70303) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 70303) = 1/(70303 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2654940809 / 1000000000) (-530988161 / 200000000) (Real.log (70303 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (164484383 / 250000000) ≤ -Real.log (500000 / 965403) ∧
    -Real.log (500000 / 965403) ≤ (657937533 / 1000000000) := by
  have h := checkLog_sound (w := (465403 / 1465403)) (n := 12)
    (lo := (164484383 / 250000000)) (hi := (657937533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((965403 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(965403 / 500000) = 1/(500000 / 965403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (164484383 / 250000000) (657937533 / 1000000000) (Real.log (965403 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (965403 / 500000) = -Real.log (500000 / 965403) := by
    rw [show ((965403 / 500000) : ℝ) = ((500000 / 965403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2670841123 / 1000000000) ≤ -Real.log (34597 / 500000) ∧
    -Real.log (34597 / 500000) ≤ (2670841127 / 1000000000) := by
  have h := checkLog_sound (w := (27903 / 97097)) (n := 12)
    (lo := (591399583 / 1000000000)) (hi := (18481237 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34597) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 34597) = 1/(34597 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2670841127 / 1000000000) (-2670841123 / 1000000000) (Real.log (34597 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1669367411 / 500000000) ≤ -Real.log (125000000000 / 3522930893597) ∧
    -Real.log (125000000000 / 3522930893597) ≤ (3338734827 / 1000000000) := by
  have h := checkLog_sound (w := (1522930893597 / 5522930893597)) (n := 12)
    (lo := (283073051 / 500000000)) (hi := (566146103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3522930893597 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3522930893597 / 2000000000000) = 1/(125000000000 / 3522930893597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1669367411 / 500000000) (3338734827 / 1000000000) (Real.log (3522930893597 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3522930893597 / 125000000000) = -Real.log (125000000000 / 3522930893597) := by
    rw [show ((3522930893597 / 125000000000) : ℝ) = ((125000000000 / 3522930893597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (670912969 / 200000000) ≤ -Real.log (250000000000 / 7158285426421) ∧
    -Real.log (250000000000 / 7158285426421) ≤ (67091297 / 20000000) := by
  have h := checkLog_sound (w := (3158285426421 / 11158285426421)) (n := 12)
    (lo := (4655809 / 8000000)) (hi := (290988063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7158285426421 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7158285426421 / 4000000000000) = 1/(250000000000 / 7158285426421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (670912969 / 200000000) (67091297 / 20000000) (Real.log (7158285426421 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7158285426421 / 250000000000) = -Real.log (250000000000 / 7158285426421) := by
    rw [show ((7158285426421 / 250000000000) : ℝ) = ((250000000000 / 7158285426421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16561519 / 5000000) ≤ -Real.log (500000000000 / 13724144062131) ∧
    -Real.log (500000000000 / 13724144062131) ≤ (662460761 / 200000000) := by
  have h := checkLog_sound (w := (5724144062131 / 21724144062131)) (n := 12)
    (lo := (13492877 / 25000000)) (hi := (539715081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13724144062131 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13724144062131 / 8000000000000) = 1/(500000000000 / 13724144062131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (16561519 / 5000000) (662460761 / 200000000) (Real.log (13724144062131 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (13724144062131 / 500000000000) = -Real.log (500000000000 / 13724144062131) := by
    rw [show ((13724144062131 / 500000000000) : ℝ) = ((500000000000 / 13724144062131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (665755731 / 200000000) ≤ -Real.log (500000000000 / 13952120126023) ∧
    -Real.log (500000000000 / 13952120126023) ≤ (166438933 / 50000000) := by
  have h := checkLog_sound (w := (5952120126023 / 21952120126023)) (n := 12)
    (lo := (111237987 / 200000000)) (hi := (34761871 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13952120126023 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13952120126023 / 8000000000000) = 1/(500000000000 / 13952120126023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (665755731 / 200000000) (166438933 / 50000000) (Real.log (13952120126023 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (13952120126023 / 500000000000) = -Real.log (500000000000 / 13952120126023) := by
    rw [show ((13952120126023 / 500000000000) : ℝ) = ((500000000000 / 13952120126023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0156
