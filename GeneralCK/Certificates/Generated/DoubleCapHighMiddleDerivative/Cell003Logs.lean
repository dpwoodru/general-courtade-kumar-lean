import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell003
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

theorem reflection_log_1_neg : (45003359 / 200000000) ≤ -Real.log (1280 / 1603) ∧
    -Real.log (1280 / 1603) ≤ (56254199 / 250000000) := by
  have h := checkLog_sound (w := (323 / 2883)) (n := 12)
    (lo := (45003359 / 200000000)) (hi := (56254199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1603 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1603 / 1280) = 1/(1280 / 1603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (45003359 / 200000000) (56254199 / 250000000) (Real.log (1603 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1603 / 1280) = -Real.log (1280 / 1603) := by
    rw [show ((1603 / 1280) : ℝ) = ((1280 / 1603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (58162393 / 200000000) ≤ -Real.log (957 / 1280) ∧
    -Real.log (957 / 1280) ≤ (145405983 / 500000000) := by
  have h := checkLog_sound (w := (323 / 2237)) (n := 12)
    (lo := (58162393 / 200000000)) (hi := (145405983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 957) = 1/(957 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-145405983 / 500000000) (-58162393 / 200000000) (Real.log (957 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (224548813 / 1000000000) ≤ -Real.log (5120 / 6409) ∧
    -Real.log (5120 / 6409) ≤ (112274407 / 500000000) := by
  have h := checkLog_sound (w := (1289 / 11529)) (n := 12)
    (lo := (224548813 / 1000000000)) (hi := (112274407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6409 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6409 / 5120) = 1/(5120 / 6409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (224548813 / 1000000000) (112274407 / 500000000) (Real.log (6409 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6409 / 5120) = -Real.log (5120 / 6409) := by
    rw [show ((6409 / 5120) : ℝ) = ((5120 / 6409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (290028573 / 1000000000) ≤ -Real.log (3831 / 5120) ∧
    -Real.log (3831 / 5120) ≤ (145014287 / 500000000) := by
  have h := checkLog_sound (w := (1289 / 8951)) (n := 12)
    (lo := (290028573 / 1000000000)) (hi := (145014287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3831) = 1/(3831 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-145014287 / 500000000) (-290028573 / 1000000000) (Real.log (3831 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (8212207 / 50000000) ≤ -Real.log (500000 / 589251) ∧
    -Real.log (500000 / 589251) ≤ (164244141 / 1000000000) := by
  have h := checkLog_sound (w := (89251 / 1089251)) (n := 12)
    (lo := (8212207 / 50000000)) (hi := (164244141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589251 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589251 / 500000) = 1/(500000 / 589251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (8212207 / 50000000) (164244141 / 1000000000) (Real.log (589251 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (589251 / 500000) = -Real.log (500000 / 589251) := by
    rw [show ((589251 / 500000) : ℝ) = ((500000 / 589251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (12289111 / 62500000) ≤ -Real.log (410749 / 500000) ∧
    -Real.log (410749 / 500000) ≤ (196625777 / 1000000000) := by
  have h := checkLog_sound (w := (89251 / 910749)) (n := 12)
    (lo := (12289111 / 62500000)) (hi := (196625777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 410749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 410749) = 1/(410749 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-196625777 / 1000000000) (-12289111 / 62500000) (Real.log (410749 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (164599613 / 1000000000) ≤ -Real.log (1000000 / 1178921) ∧
    -Real.log (1000000 / 1178921) ≤ (82299807 / 500000000) := by
  have h := checkLog_sound (w := (178921 / 2178921)) (n := 12)
    (lo := (164599613 / 1000000000)) (hi := (82299807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1178921 / 1000000) = 1/(1000000 / 1178921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (164599613 / 1000000000) (82299807 / 500000000) (Real.log (1178921 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1178921 / 1000000) = -Real.log (1000000 / 1178921) := by
    rw [show ((1178921 / 1000000) : ℝ) = ((1000000 / 1178921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3942719 / 20000000) ≤ -Real.log (821079 / 1000000) ∧
    -Real.log (821079 / 1000000) ≤ (197135951 / 1000000000) := by
  have h := checkLog_sound (w := (178921 / 1821079)) (n := 12)
    (lo := (3942719 / 20000000)) (hi := (197135951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 821079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 821079) = 1/(821079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-197135951 / 1000000000) (-3942719 / 20000000) (Real.log (821079 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (11986531 / 100000000) ≤ -Real.log (200000 / 225469) ∧
    -Real.log (200000 / 225469) ≤ (119865311 / 1000000000) := by
  have h := checkLog_sound (w := (25469 / 425469)) (n := 12)
    (lo := (11986531 / 100000000)) (hi := (119865311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225469 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225469 / 200000) = 1/(200000 / 225469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (11986531 / 100000000) (119865311 / 1000000000) (Real.log (225469 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (225469 / 200000) = -Real.log (200000 / 225469) := by
    rw [show ((225469 / 200000) : ℝ) = ((200000 / 225469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (13621499 / 100000000) ≤ -Real.log (174531 / 200000) ∧
    -Real.log (174531 / 200000) ≤ (136214991 / 1000000000) := by
  have h := checkLog_sound (w := (25469 / 374531)) (n := 12)
    (lo := (13621499 / 100000000)) (hi := (136214991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 174531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 174531) = 1/(174531 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-136214991 / 1000000000) (-13621499 / 100000000) (Real.log (174531 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (60067467 / 500000000) ≤ -Real.log (1000000 / 1127649) ∧
    -Real.log (1000000 / 1127649) ≤ (24026987 / 200000000) := by
  have h := checkLog_sound (w := (127649 / 2127649)) (n := 12)
    (lo := (60067467 / 500000000)) (hi := (24026987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127649 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1127649 / 1000000) = 1/(1000000 / 1127649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (60067467 / 500000000) (24026987 / 200000000) (Real.log (1127649 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1127649 / 1000000) = -Real.log (1000000 / 1127649) := by
    rw [show ((1127649 / 1000000) : ℝ) = ((1000000 / 1127649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (136563413 / 1000000000) ≤ -Real.log (872351 / 1000000) ∧
    -Real.log (872351 / 1000000) ≤ (68281707 / 500000000) := by
  have h := checkLog_sound (w := (127649 / 1872351)) (n := 12)
    (lo := (136563413 / 1000000000)) (hi := (68281707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 872351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 872351) = 1/(872351 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-68281707 / 500000000) (-136563413 / 1000000000) (Real.log (872351 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (257288693 / 500000000) ≤ -Real.log (250000000000 / 418232837379) ∧
    -Real.log (250000000000 / 418232837379) ≤ (514577387 / 1000000000) := by
  have h := checkLog_sound (w := (168232837379 / 668232837379)) (n := 12)
    (lo := (257288693 / 500000000)) (hi := (514577387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((418232837379 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(418232837379 / 250000000000) = 1/(250000000000 / 418232837379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (257288693 / 500000000) (514577387 / 1000000000) (Real.log (418232837379 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (418232837379 / 250000000000) = -Real.log (250000000000 / 418232837379) := by
    rw [show ((418232837379 / 250000000000) : ℝ) = ((250000000000 / 418232837379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (515828761 / 1000000000) ≤ -Real.log (500000000000 / 837513061651) ∧
    -Real.log (500000000000 / 837513061651) ≤ (257914381 / 500000000) := by
  have h := checkLog_sound (w := (337513061651 / 1337513061651)) (n := 12)
    (lo := (515828761 / 1000000000)) (hi := (257914381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((837513061651 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(837513061651 / 500000000000) = 1/(500000000000 / 837513061651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (515828761 / 1000000000) (257914381 / 500000000) (Real.log (837513061651 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (837513061651 / 500000000000) = -Real.log (500000000000 / 837513061651) := by
    rw [show ((837513061651 / 500000000000) : ℝ) = ((500000000000 / 837513061651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (90217479 / 250000000) ≤ -Real.log (500000000000 / 717288417013) ∧
    -Real.log (500000000000 / 717288417013) ≤ (360869917 / 1000000000) := by
  have h := checkLog_sound (w := (217288417013 / 1217288417013)) (n := 12)
    (lo := (90217479 / 250000000)) (hi := (360869917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717288417013 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717288417013 / 500000000000) = 1/(500000000000 / 717288417013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (90217479 / 250000000) (360869917 / 1000000000) (Real.log (717288417013 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (717288417013 / 500000000000) = -Real.log (500000000000 / 717288417013) := by
    rw [show ((717288417013 / 500000000000) : ℝ) = ((500000000000 / 717288417013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (361735563 / 1000000000) ≤ -Real.log (250000000000 / 358954802157) ∧
    -Real.log (250000000000 / 358954802157) ≤ (90433891 / 250000000) := by
  have h := checkLog_sound (w := (108954802157 / 608954802157)) (n := 12)
    (lo := (361735563 / 1000000000)) (hi := (90433891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358954802157 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358954802157 / 250000000000) = 1/(250000000000 / 358954802157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (361735563 / 1000000000) (90433891 / 250000000) (Real.log (358954802157 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (358954802157 / 250000000000) = -Real.log (250000000000 / 358954802157) := by
    rw [show ((358954802157 / 250000000000) : ℝ) = ((250000000000 / 358954802157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (2560803 / 10000000) ≤ -Real.log (250000000000 / 322964115257) ∧
    -Real.log (250000000000 / 322964115257) ≤ (256080301 / 1000000000) := by
  have h := checkLog_sound (w := (72964115257 / 572964115257)) (n := 12)
    (lo := (2560803 / 10000000)) (hi := (256080301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322964115257 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322964115257 / 250000000000) = 1/(250000000000 / 322964115257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2560803 / 10000000) (256080301 / 1000000000) (Real.log (322964115257 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (322964115257 / 250000000000) = -Real.log (250000000000 / 322964115257) := by
    rw [show ((322964115257 / 250000000000) : ℝ) = ((250000000000 / 322964115257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (256698347 / 1000000000) ≤ -Real.log (62500000000 / 80790945961) ∧
    -Real.log (62500000000 / 80790945961) ≤ (64174587 / 250000000) := by
  have h := checkLog_sound (w := (18290945961 / 143290945961)) (n := 12)
    (lo := (256698347 / 1000000000)) (hi := (64174587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80790945961 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80790945961 / 62500000000) = 1/(62500000000 / 80790945961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (256698347 / 1000000000) (64174587 / 250000000) (Real.log (80790945961 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (80790945961 / 62500000000) = -Real.log (62500000000 / 80790945961) := by
    rw [show ((80790945961 / 62500000000) : ℝ) = ((62500000000 / 80790945961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8214239 / 500000000) ≤ -Real.log (983705732799 / 1000000000000) ∧
    -Real.log (983705732799 / 1000000000000) ≤ (16428479 / 1000000000) := by
  have h := checkLog_sound (w := (16294267201 / 1983705732799)) (n := 12)
    (lo := (8214239 / 500000000)) (hi := (16428479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983705732799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983705732799) = 1/(983705732799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16428479 / 1000000000) (-8214239 / 500000000) (Real.log (983705732799 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16349679 / 1000000000) ≤ -Real.log (39351330039 / 40000000000) ∧
    -Real.log (39351330039 / 40000000000) ≤ (204371 / 12500000) := by
  have h := checkLog_sound (w := (648669961 / 79351330039)) (n := 12)
    (lo := (16349679 / 1000000000)) (hi := (204371 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39351330039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39351330039) = 1/(39351330039 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-204371 / 12500000) (-16349679 / 1000000000) (Real.log (39351330039 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell003
