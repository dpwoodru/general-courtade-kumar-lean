import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell007
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

theorem reflection_log_1_neg : (226886537 / 1000000000) ≤ -Real.log (640 / 803) ∧
    -Real.log (640 / 803) ≤ (113443269 / 500000000) := by
  have h := checkLog_sound (w := (163 / 1443)) (n := 12)
    (lo := (226886537 / 1000000000)) (hi := (113443269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803 / 640) = 1/(640 / 803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (226886537 / 1000000000) (113443269 / 500000000) (Real.log (803 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (803 / 640) = -Real.log (640 / 803) := by
    rw [show ((803 / 640) : ℝ) = ((640 / 803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (58790337 / 200000000) ≤ -Real.log (477 / 640) ∧
    -Real.log (477 / 640) ≤ (146975843 / 500000000) := by
  have h := checkLog_sound (w := (163 / 1117)) (n := 12)
    (lo := (58790337 / 200000000)) (hi := (146975843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 477) = 1/(477 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-146975843 / 500000000) (-58790337 / 200000000) (Real.log (477 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (226419429 / 1000000000) ≤ -Real.log (5120 / 6421) ∧
    -Real.log (5120 / 6421) ≤ (22641943 / 100000000) := by
  have h := checkLog_sound (w := (1301 / 11541)) (n := 12)
    (lo := (226419429 / 1000000000)) (hi := (22641943 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6421 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6421 / 5120) = 1/(5120 / 6421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (226419429 / 1000000000) (22641943 / 100000000) (Real.log (6421 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6421 / 5120) = -Real.log (5120 / 6421) := by
    rw [show ((6421 / 5120) : ℝ) = ((5120 / 6421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (29316583 / 100000000) ≤ -Real.log (3819 / 5120) ∧
    -Real.log (3819 / 5120) ≤ (293165831 / 1000000000) := by
  have h := checkLog_sound (w := (1301 / 8939)) (n := 12)
    (lo := (29316583 / 100000000)) (hi := (293165831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3819) = 1/(3819 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-293165831 / 1000000000) (-29316583 / 100000000) (Real.log (3819 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (165661037 / 1000000000) ≤ -Real.log (1000000 / 1180173) ∧
    -Real.log (1000000 / 1180173) ≤ (82830519 / 500000000) := by
  have h := checkLog_sound (w := (180173 / 2180173)) (n := 12)
    (lo := (165661037 / 1000000000)) (hi := (82830519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1180173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1180173 / 1000000) = 1/(1000000 / 1180173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (165661037 / 1000000000) (82830519 / 500000000) (Real.log (1180173 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1180173 / 1000000) = -Real.log (1000000 / 1180173) := by
    rw [show ((1180173 / 1000000) : ℝ) = ((1000000 / 1180173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (12416371 / 62500000) ≤ -Real.log (819827 / 1000000) ∧
    -Real.log (819827 / 1000000) ≤ (198661937 / 1000000000) := by
  have h := checkLog_sound (w := (180173 / 1819827)) (n := 12)
    (lo := (12416371 / 62500000)) (hi := (198661937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 819827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 819827) = 1/(819827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-198661937 / 1000000000) (-12416371 / 62500000) (Real.log (819827 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (166016007 / 1000000000) ≤ -Real.log (62500 / 73787) ∧
    -Real.log (62500 / 73787) ≤ (20752001 / 125000000) := by
  have h := checkLog_sound (w := (11287 / 136287)) (n := 12)
    (lo := (166016007 / 1000000000)) (hi := (20752001 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73787 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73787 / 62500) = 1/(62500 / 73787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (166016007 / 1000000000) (20752001 / 125000000) (Real.log (73787 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (73787 / 62500) = -Real.log (62500 / 73787) := by
    rw [show ((73787 / 62500) : ℝ) = ((62500 / 73787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3983463 / 20000000) ≤ -Real.log (51213 / 62500) ∧
    -Real.log (51213 / 62500) ≤ (199173151 / 1000000000) := by
  have h := checkLog_sound (w := (11287 / 113713)) (n := 12)
    (lo := (3983463 / 20000000)) (hi := (199173151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 51213) = 1/(51213 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-199173151 / 1000000000) (-3983463 / 20000000) (Real.log (51213 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (120940711 / 1000000000) ≤ -Real.log (500000 / 564279) ∧
    -Real.log (500000 / 564279) ≤ (15117589 / 125000000) := by
  have h := checkLog_sound (w := (64279 / 1064279)) (n := 12)
    (lo := (120940711 / 1000000000)) (hi := (15117589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((564279 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(564279 / 500000) = 1/(500000 / 564279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (120940711 / 1000000000) (15117589 / 125000000) (Real.log (564279 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (564279 / 500000) = -Real.log (500000 / 564279) := by
    rw [show ((564279 / 500000) : ℝ) = ((500000 / 564279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8600373 / 62500000) ≤ -Real.log (435721 / 500000) ∧
    -Real.log (435721 / 500000) ≤ (137605969 / 1000000000) := by
  have h := checkLog_sound (w := (64279 / 935721)) (n := 12)
    (lo := (8600373 / 62500000)) (hi := (137605969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 435721) = 1/(435721 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-137605969 / 1000000000) (-8600373 / 62500000) (Real.log (435721 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (121210931 / 1000000000) ≤ -Real.log (1000000 / 1128863) ∧
    -Real.log (1000000 / 1128863) ≤ (30302733 / 250000000) := by
  have h := checkLog_sound (w := (128863 / 2128863)) (n := 12)
    (lo := (121210931 / 1000000000)) (hi := (30302733 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1128863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1128863 / 1000000) = 1/(1000000 / 1128863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (121210931 / 1000000000) (30302733 / 250000000) (Real.log (1128863 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1128863 / 1000000) = -Real.log (1000000 / 1128863) := by
    rw [show ((1128863 / 1000000) : ℝ) = ((1000000 / 1128863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (17244503 / 125000000) ≤ -Real.log (871137 / 1000000) ∧
    -Real.log (871137 / 1000000) ≤ (5518241 / 40000000) := by
  have h := checkLog_sound (w := (128863 / 1871137)) (n := 12)
    (lo := (17244503 / 125000000)) (hi := (5518241 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 871137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 871137) = 1/(871137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-5518241 / 40000000) (-17244503 / 125000000) (Real.log (871137 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (25979263 / 50000000) ≤ -Real.log (250000000000 / 420332547787) ∧
    -Real.log (250000000000 / 420332547787) ≤ (519585261 / 1000000000) := by
  have h := checkLog_sound (w := (170332547787 / 670332547787)) (n := 12)
    (lo := (25979263 / 50000000)) (hi := (519585261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((420332547787 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(420332547787 / 250000000000) = 1/(250000000000 / 420332547787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (25979263 / 50000000) (519585261 / 1000000000) (Real.log (420332547787 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (420332547787 / 250000000000) = -Real.log (250000000000 / 420332547787) := by
    rw [show ((420332547787 / 250000000000) : ℝ) = ((250000000000 / 420332547787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (520838223 / 1000000000) ≤ -Real.log (500000000000 / 841719077569) ∧
    -Real.log (500000000000 / 841719077569) ≤ (32552389 / 62500000) := by
  have h := checkLog_sound (w := (341719077569 / 1341719077569)) (n := 12)
    (lo := (520838223 / 1000000000)) (hi := (32552389 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((841719077569 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(841719077569 / 500000000000) = 1/(500000000000 / 841719077569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (520838223 / 1000000000) (32552389 / 62500000) (Real.log (841719077569 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (841719077569 / 500000000000) = -Real.log (500000000000 / 841719077569) := by
    rw [show ((841719077569 / 500000000000) : ℝ) = ((500000000000 / 841719077569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (182161487 / 500000000) ≤ -Real.log (500000000000 / 719769536743) ∧
    -Real.log (500000000000 / 719769536743) ≤ (14572919 / 40000000) := by
  have h := checkLog_sound (w := (219769536743 / 1219769536743)) (n := 12)
    (lo := (182161487 / 500000000)) (hi := (14572919 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719769536743 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719769536743 / 500000000000) = 1/(500000000000 / 719769536743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (182161487 / 500000000) (14572919 / 40000000) (Real.log (719769536743 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (719769536743 / 500000000000) = -Real.log (500000000000 / 719769536743) := by
    rw [show ((719769536743 / 500000000000) : ℝ) = ((500000000000 / 719769536743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (182594579 / 500000000) ≤ -Real.log (125000000000 / 180098314881) ∧
    -Real.log (125000000000 / 180098314881) ≤ (365189159 / 1000000000) := by
  have h := checkLog_sound (w := (55098314881 / 305098314881)) (n := 12)
    (lo := (182594579 / 500000000)) (hi := (365189159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180098314881 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180098314881 / 125000000000) = 1/(125000000000 / 180098314881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (182594579 / 500000000) (365189159 / 1000000000) (Real.log (180098314881 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (180098314881 / 125000000000) = -Real.log (125000000000 / 180098314881) := by
    rw [show ((180098314881 / 125000000000) : ℝ) = ((125000000000 / 180098314881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (258546679 / 1000000000) ≤ -Real.log (25000000000 / 32376165023) ∧
    -Real.log (25000000000 / 32376165023) ≤ (6463667 / 25000000) := by
  have h := checkLog_sound (w := (7376165023 / 57376165023)) (n := 12)
    (lo := (258546679 / 1000000000)) (hi := (6463667 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32376165023 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32376165023 / 25000000000) = 1/(25000000000 / 32376165023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (258546679 / 1000000000) (6463667 / 25000000) (Real.log (32376165023 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (32376165023 / 25000000000) = -Real.log (25000000000 / 32376165023) := by
    rw [show ((32376165023 / 25000000000) : ℝ) = ((25000000000 / 32376165023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (51833391 / 200000000) ≤ -Real.log (125000000000 / 161981267011) ∧
    -Real.log (125000000000 / 161981267011) ≤ (64791739 / 250000000) := by
  have h := checkLog_sound (w := (36981267011 / 286981267011)) (n := 12)
    (lo := (51833391 / 200000000)) (hi := (64791739 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161981267011 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161981267011 / 125000000000) = 1/(125000000000 / 161981267011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (51833391 / 200000000) (64791739 / 250000000) (Real.log (161981267011 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (161981267011 / 125000000000) = -Real.log (125000000000 / 161981267011) := by
    rw [show ((161981267011 / 125000000000) : ℝ) = ((125000000000 / 161981267011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4186273 / 250000000) ≤ -Real.log (983394327231 / 1000000000000) ∧
    -Real.log (983394327231 / 1000000000000) ≤ (16745093 / 1000000000) := by
  have h := checkLog_sound (w := (16605672769 / 1983394327231)) (n := 12)
    (lo := (4186273 / 250000000)) (hi := (16745093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983394327231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983394327231) = 1/(983394327231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16745093 / 1000000000) (-4186273 / 250000000) (Real.log (983394327231 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2083157 / 125000000) ≤ -Real.log (245868210159 / 250000000000) ∧
    -Real.log (245868210159 / 250000000000) ≤ (16665257 / 1000000000) := by
  have h := checkLog_sound (w := (4131789841 / 495868210159)) (n := 12)
    (lo := (2083157 / 125000000)) (hi := (16665257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245868210159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245868210159) = 1/(245868210159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-16665257 / 1000000000) (-2083157 / 125000000) (Real.log (245868210159 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell007
