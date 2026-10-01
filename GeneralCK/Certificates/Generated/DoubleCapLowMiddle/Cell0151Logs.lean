import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0151
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

theorem reflection_log_1_neg : (652650653 / 1000000000) ≤ -Real.log (1600 / 3073) ∧
    -Real.log (1600 / 3073) ≤ (326325327 / 500000000) := by
  have h := checkLog_sound (w := (1473 / 4673)) (n := 12)
    (lo := (652650653 / 1000000000)) (hi := (326325327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3073 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3073 / 1600) = 1/(1600 / 3073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (652650653 / 1000000000) (326325327 / 500000000) (Real.log (3073 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3073 / 1600) = -Real.log (1600 / 3073) := by
    rw [show ((3073 / 1600) : ℝ) = ((1600 / 3073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (126678591 / 50000000) ≤ -Real.log (127 / 1600) ∧
    -Real.log (127 / 1600) ≤ (158348239 / 62500000) := by
  have h := checkLog_sound (w := (73 / 327)) (n := 12)
    (lo := (11353257 / 25000000)) (hi := (454130281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 127) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 127) = 1/(127 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-158348239 / 62500000) (-126678591 / 50000000) (Real.log (127 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (325938747 / 500000000) ≤ -Real.log (2560 / 4913) ∧
    -Real.log (2560 / 4913) ≤ (130375499 / 200000000) := by
  have h := checkLog_sound (w := (2353 / 7473)) (n := 12)
    (lo := (325938747 / 500000000)) (hi := (130375499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4913 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4913 / 2560) = 1/(2560 / 4913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (325938747 / 500000000) (130375499 / 200000000) (Real.log (4913 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (4913 / 2560) = -Real.log (2560 / 4913) := by
    rw [show ((4913 / 2560) : ℝ) = ((2560 / 4913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1257521871 / 500000000) ≤ -Real.log (207 / 2560) ∧
    -Real.log (207 / 2560) ≤ (1257521873 / 500000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 207) = 1/(207 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1257521873 / 500000000) (-1257521871 / 500000000) (Real.log (207 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (38152793 / 62500000) ≤ -Real.log (800 / 1473) ∧
    -Real.log (800 / 1473) ≤ (610444689 / 1000000000) := by
  have h := checkLog_sound (w := (673 / 2273)) (n := 12)
    (lo := (38152793 / 62500000)) (hi := (610444689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1473 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1473 / 800) = 1/(800 / 1473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (38152793 / 62500000) (610444689 / 1000000000) (Real.log (1473 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1473 / 800) = -Real.log (800 / 1473) := by
    rw [show ((1473 / 800) : ℝ) = ((800 / 1473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (5751327 / 3125000) ≤ -Real.log (127 / 800) ∧
    -Real.log (127 / 800) ≤ (1840424643 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 327)) (n := 12)
    (lo := (11353257 / 25000000)) (hi := (454130281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 127) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 127) = 1/(127 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1840424643 / 1000000000) (-5751327 / 3125000) (Real.log (127 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (608831031 / 1000000000) ≤ -Real.log (1280 / 2353) ∧
    -Real.log (1280 / 2353) ≤ (76103879 / 125000000) := by
  have h := checkLog_sound (w := (1073 / 3633)) (n := 12)
    (lo := (608831031 / 1000000000)) (hi := (76103879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2353 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2353 / 1280) = 1/(1280 / 2353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (608831031 / 1000000000) (76103879 / 125000000) (Real.log (2353 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2353 / 1280) = -Real.log (1280 / 2353) := by
    rw [show ((2353 / 1280) : ℝ) = ((1280 / 2353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (910948281 / 500000000) ≤ -Real.log (207 / 1280) ∧
    -Real.log (207 / 1280) ≤ (364379313 / 200000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 207) = 1/(207 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-364379313 / 200000000) (-910948281 / 500000000) (Real.log (207 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (660985493 / 1000000000) ≤ -Real.log (10000 / 19367) ∧
    -Real.log (10000 / 19367) ≤ (330492747 / 500000000) := by
  have h := checkLog_sound (w := (9367 / 29367)) (n := 12)
    (lo := (660985493 / 1000000000)) (hi := (330492747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19367 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19367 / 10000) = 1/(10000 / 19367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (660985493 / 1000000000) (330492747 / 500000000) (Real.log (19367 / 10000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (19367 / 10000) = -Real.log (10000 / 19367) := by
    rw [show ((19367 / 10000) : ℝ) = ((10000 / 19367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (689967487 / 250000000) ≤ -Real.log (633 / 10000) ∧
    -Real.log (633 / 10000) ≤ (5390371 / 1953125) := by
  have h := checkLog_sound (w := (617 / 1883)) (n := 12)
    (lo := (85053551 / 125000000)) (hi := (680428409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 633) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1250 / 633) = 1/(633 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-5390371 / 1953125) (-689967487 / 250000000) (Real.log (633 / 10000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (330765559 / 500000000) ≤ -Real.log (1000000 / 1937757) ∧
    -Real.log (1000000 / 1937757) ≤ (661531119 / 1000000000) := by
  have h := checkLog_sound (w := (937757 / 2937757)) (n := 12)
    (lo := (330765559 / 500000000)) (hi := (661531119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1937757 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1937757 / 1000000) = 1/(1000000 / 1937757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (330765559 / 500000000) (661531119 / 1000000000) (Real.log (1937757 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1937757 / 1000000) = -Real.log (1000000 / 1937757) := by
    rw [show ((1937757 / 1000000) : ℝ) = ((1000000 / 1937757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2776709197 / 1000000000) ≤ -Real.log (62243 / 1000000) ∧
    -Real.log (62243 / 1000000) ≤ (1388354601 / 500000000) := by
  have h := checkLog_sound (w := (257 / 124743)) (n := 12)
    (lo := (4120477 / 1000000000)) (hi := (2060239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62243) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 62243) = 1/(62243 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1388354601 / 500000000) (-2776709197 / 1000000000) (Real.log (62243 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (6602391 / 10000000) ≤ -Real.log (200000 / 387051) ∧
    -Real.log (200000 / 387051) ≤ (660239101 / 1000000000) := by
  have h := checkLog_sound (w := (187051 / 587051)) (n := 12)
    (lo := (6602391 / 10000000)) (hi := (660239101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387051 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387051 / 200000) = 1/(200000 / 387051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (6602391 / 10000000) (660239101 / 1000000000) (Real.log (387051 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (387051 / 200000) = -Real.log (200000 / 387051) := by
    rw [show ((387051 / 200000) : ℝ) = ((200000 / 387051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2737298799 / 1000000000) ≤ -Real.log (12949 / 200000) ∧
    -Real.log (12949 / 200000) ≤ (2737298803 / 1000000000) := by
  have h := checkLog_sound (w := (12051 / 37949)) (n := 12)
    (lo := (657857259 / 1000000000)) (hi := (32892863 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 12949) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 12949) = 1/(12949 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2737298803 / 1000000000) (-2737298799 / 1000000000) (Real.log (12949 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (132163327 / 200000000) ≤ -Real.log (1000000 / 1936373) ∧
    -Real.log (1000000 / 1936373) ≤ (165204159 / 250000000) := by
  have h := checkLog_sound (w := (936373 / 2936373)) (n := 12)
    (lo := (132163327 / 200000000)) (hi := (165204159 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1936373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1936373 / 1000000) = 1/(1000000 / 1936373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (132163327 / 200000000) (165204159 / 250000000) (Real.log (1936373 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1936373 / 1000000) = -Real.log (1000000 / 1936373) := by
    rw [show ((1936373 / 1000000) : ℝ) = ((1000000 / 1936373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (344339671 / 125000000) ≤ -Real.log (63627 / 1000000) ∧
    -Real.log (63627 / 1000000) ≤ (688679343 / 250000000) := by
  have h := checkLog_sound (w := (61373 / 188627)) (n := 12)
    (lo := (168818957 / 250000000)) (hi := (675275829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 63627) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 63627) = 1/(63627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-688679343 / 250000000) (-344339671 / 125000000) (Real.log (63627 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3420855441 / 1000000000) ≤ -Real.log (125000000000 / 3824447077409) ∧
    -Real.log (125000000000 / 3824447077409) ≤ (1710427723 / 500000000) := by
  have h := checkLog_sound (w := (1824447077409 / 5824447077409)) (n := 12)
    (lo := (648266721 / 1000000000)) (hi := (324133361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3824447077409 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3824447077409 / 2000000000000) = 1/(125000000000 / 3824447077409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3420855441 / 1000000000) (1710427723 / 500000000) (Real.log (3824447077409 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3824447077409 / 125000000000) = -Real.log (125000000000 / 3824447077409) := by
    rw [show ((3824447077409 / 125000000000) : ℝ) = ((125000000000 / 3824447077409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (859560079 / 250000000) ≤ -Real.log (100000000000 / 3113212730749) ∧
    -Real.log (100000000000 / 3113212730749) ≤ (3438240321 / 1000000000) := by
  have h := checkLog_sound (w := (1513212730749 / 4713212730749)) (n := 12)
    (lo := (166412899 / 250000000)) (hi := (665651597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3113212730749 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3113212730749 / 1600000000000) = 1/(100000000000 / 3113212730749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (859560079 / 250000000) (3438240321 / 1000000000) (Real.log (3113212730749 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3113212730749 / 100000000000) = -Real.log (100000000000 / 3113212730749) := by
    rw [show ((3113212730749 / 100000000000) : ℝ) = ((100000000000 / 3113212730749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3397537899 / 1000000000) ≤ -Real.log (500000000000 / 14945208124179) ∧
    -Real.log (500000000000 / 14945208124179) ≤ (212346119 / 62500000) := by
  have h := checkLog_sound (w := (6945208124179 / 22945208124179)) (n := 12)
    (lo := (624949179 / 1000000000)) (hi := (31247459 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14945208124179 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(14945208124179 / 8000000000000) = 1/(500000000000 / 14945208124179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3397537899 / 1000000000) (212346119 / 62500000) (Real.log (14945208124179 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (14945208124179 / 500000000000) = -Real.log (500000000000 / 14945208124179) := by
    rw [show ((14945208124179 / 500000000000) : ℝ) = ((500000000000 / 14945208124179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3415534003 / 1000000000) ≤ -Real.log (100000000000 / 3043319659893) ∧
    -Real.log (100000000000 / 3043319659893) ≤ (426941751 / 125000000) := by
  have h := checkLog_sound (w := (1443319659893 / 4643319659893)) (n := 12)
    (lo := (642945283 / 1000000000)) (hi := (160736321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3043319659893 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3043319659893 / 1600000000000) = 1/(100000000000 / 3043319659893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3415534003 / 1000000000) (426941751 / 125000000) (Real.log (3043319659893 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3043319659893 / 100000000000) = -Real.log (100000000000 / 3043319659893) := by
    rw [show ((3043319659893 / 100000000000) : ℝ) = ((100000000000 / 3043319659893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0151
