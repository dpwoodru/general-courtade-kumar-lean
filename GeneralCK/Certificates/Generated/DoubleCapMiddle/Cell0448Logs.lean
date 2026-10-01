import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0448
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

theorem reflection_log_1_neg : (188649151 / 1000000000) ≤ -Real.log (5120 / 6183) ∧
    -Real.log (5120 / 6183) ≤ (2947643 / 15625000) := by
  have h := checkLog_sound (w := (1063 / 11303)) (n := 12)
    (lo := (188649151 / 1000000000)) (hi := (2947643 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6183 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6183 / 5120) = 1/(5120 / 6183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (188649151 / 1000000000) (2947643 / 15625000) (Real.log (6183 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6183 / 5120) = -Real.log (5120 / 6183) := by
    rw [show ((6183 / 5120) : ℝ) = ((5120 / 6183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (116355327 / 500000000) ≤ -Real.log (4057 / 5120) ∧
    -Real.log (4057 / 5120) ≤ (46542131 / 200000000) := by
  have h := checkLog_sound (w := (1063 / 9177)) (n := 12)
    (lo := (116355327 / 500000000)) (hi := (46542131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4057) = 1/(4057 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-46542131 / 200000000) (-116355327 / 500000000) (Real.log (4057 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (188406521 / 1000000000) ≤ -Real.log (10240 / 12363) ∧
    -Real.log (10240 / 12363) ≤ (94203261 / 500000000) := by
  have h := checkLog_sound (w := (2123 / 22603)) (n := 12)
    (lo := (188406521 / 1000000000)) (hi := (94203261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12363 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12363 / 10240) = 1/(10240 / 12363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (188406521 / 1000000000) (94203261 / 500000000) (Real.log (12363 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12363 / 10240) = -Real.log (10240 / 12363) := by
    rw [show ((12363 / 10240) : ℝ) = ((10240 / 12363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (232340991 / 1000000000) ≤ -Real.log (8117 / 10240) ∧
    -Real.log (8117 / 10240) ≤ (453791 / 1953125) := by
  have h := checkLog_sound (w := (2123 / 18357)) (n := 12)
    (lo := (232340991 / 1000000000)) (hi := (453791 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8117) = 1/(8117 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-453791 / 1953125) (-232340991 / 1000000000) (Real.log (8117 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (347295153 / 1000000000) ≤ -Real.log (2560 / 3623) ∧
    -Real.log (2560 / 3623) ≤ (173647577 / 500000000) := by
  have h := checkLog_sound (w := (1063 / 6183)) (n := 12)
    (lo := (347295153 / 1000000000)) (hi := (173647577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3623 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3623 / 2560) = 1/(2560 / 3623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (347295153 / 1000000000) (173647577 / 500000000) (Real.log (3623 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3623 / 2560) = -Real.log (2560 / 3623) := by
    rw [show ((3623 / 2560) : ℝ) = ((2560 / 3623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (536544153 / 1000000000) ≤ -Real.log (1497 / 2560) ∧
    -Real.log (1497 / 2560) ≤ (268272077 / 500000000) := by
  have h := checkLog_sound (w := (1063 / 4057)) (n := 12)
    (lo := (536544153 / 1000000000)) (hi := (268272077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1497) = 1/(1497 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-268272077 / 500000000) (-536544153 / 1000000000) (Real.log (1497 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (173440523 / 500000000) ≤ -Real.log (5120 / 7243) ∧
    -Real.log (5120 / 7243) ≤ (346881047 / 1000000000) := by
  have h := checkLog_sound (w := (2123 / 12363)) (n := 12)
    (lo := (173440523 / 500000000)) (hi := (346881047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7243 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7243 / 5120) = 1/(5120 / 7243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (173440523 / 500000000) (346881047 / 1000000000) (Real.log (7243 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7243 / 5120) = -Real.log (5120 / 7243) := by
    rw [show ((7243 / 5120) : ℝ) = ((5120 / 7243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (10710853 / 20000000) ≤ -Real.log (2997 / 5120) ∧
    -Real.log (2997 / 5120) ≤ (535542651 / 1000000000) := by
  have h := checkLog_sound (w := (2123 / 8117)) (n := 12)
    (lo := (10710853 / 20000000)) (hi := (535542651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2997) = 1/(2997 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-535542651 / 1000000000) (-10710853 / 20000000) (Real.log (2997 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (10354819 / 40000000) ≤ -Real.log (500000 / 647733) ∧
    -Real.log (500000 / 647733) ≤ (64717619 / 250000000) := by
  have h := checkLog_sound (w := (147733 / 1147733)) (n := 12)
    (lo := (10354819 / 40000000)) (hi := (64717619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647733 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647733 / 500000) = 1/(500000 / 647733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (10354819 / 40000000) (64717619 / 250000000) (Real.log (647733 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (647733 / 500000) = -Real.log (500000 / 647733) := by
    rw [show ((647733 / 500000) : ℝ) = ((500000 / 647733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (350218687 / 1000000000) ≤ -Real.log (352267 / 500000) ∧
    -Real.log (352267 / 500000) ≤ (5472167 / 15625000) := by
  have h := checkLog_sound (w := (147733 / 852267)) (n := 12)
    (lo := (350218687 / 1000000000)) (hi := (5472167 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 352267) = 1/(352267 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-5472167 / 15625000) (-350218687 / 1000000000) (Real.log (352267 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (259198489 / 1000000000) ≤ -Real.log (1000000 / 1295891) ∧
    -Real.log (1000000 / 1295891) ≤ (25919849 / 100000000) := by
  have h := checkLog_sound (w := (295891 / 2295891)) (n := 12)
    (lo := (259198489 / 1000000000)) (hi := (25919849 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1295891 / 1000000) = 1/(1000000 / 1295891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (259198489 / 1000000000) (25919849 / 100000000) (Real.log (1295891 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1295891 / 1000000) = -Real.log (1000000 / 1295891) := by
    rw [show ((1295891 / 1000000) : ℝ) = ((1000000 / 1295891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (70164421 / 200000000) ≤ -Real.log (704109 / 1000000) ∧
    -Real.log (704109 / 1000000) ≤ (175411053 / 500000000) := by
  have h := checkLog_sound (w := (295891 / 1704109)) (n := 12)
    (lo := (70164421 / 200000000)) (hi := (175411053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 704109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 704109) = 1/(704109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-175411053 / 500000000) (-70164421 / 200000000) (Real.log (704109 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (38800777 / 200000000) ≤ -Real.log (1000000 / 1214101) ∧
    -Real.log (1000000 / 1214101) ≤ (97001943 / 500000000) := by
  have h := checkLog_sound (w := (214101 / 2214101)) (n := 12)
    (lo := (38800777 / 200000000)) (hi := (97001943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1214101 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1214101 / 1000000) = 1/(1000000 / 1214101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (38800777 / 200000000) (97001943 / 500000000) (Real.log (1214101 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1214101 / 1000000) = -Real.log (1000000 / 1214101) := by
    rw [show ((1214101 / 1000000) : ℝ) = ((1000000 / 1214101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (240926993 / 1000000000) ≤ -Real.log (785899 / 1000000) ∧
    -Real.log (785899 / 1000000) ≤ (120463497 / 500000000) := by
  have h := checkLog_sound (w := (214101 / 1785899)) (n := 12)
    (lo := (240926993 / 1000000000)) (hi := (120463497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 785899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 785899) = 1/(785899 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-120463497 / 500000000) (-240926993 / 1000000000) (Real.log (785899 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (194270713 / 1000000000) ≤ -Real.log (40000 / 48577) ∧
    -Real.log (40000 / 48577) ≤ (97135357 / 500000000) := by
  have h := checkLog_sound (w := (8577 / 88577)) (n := 12)
    (lo := (194270713 / 1000000000)) (hi := (97135357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48577 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48577 / 40000) = 1/(40000 / 48577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (194270713 / 1000000000) (97135357 / 500000000) (Real.log (48577 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (48577 / 40000) = -Real.log (40000 / 48577) := by
    rw [show ((48577 / 40000) : ℝ) = ((40000 / 48577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (48267869 / 200000000) ≤ -Real.log (31423 / 40000) ∧
    -Real.log (31423 / 40000) ≤ (120669673 / 500000000) := by
  have h := checkLog_sound (w := (8577 / 71423)) (n := 12)
    (lo := (48267869 / 200000000)) (hi := (120669673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31423) = 1/(31423 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-120669673 / 500000000) (-48267869 / 200000000) (Real.log (31423 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (609089163 / 1000000000) ≤ -Real.log (500000000000 / 919377915047) ∧
    -Real.log (500000000000 / 919377915047) ≤ (152272291 / 250000000) := by
  have h := checkLog_sound (w := (419377915047 / 1419377915047)) (n := 12)
    (lo := (609089163 / 1000000000)) (hi := (152272291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((919377915047 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(919377915047 / 500000000000) = 1/(500000000000 / 919377915047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (609089163 / 1000000000) (152272291 / 250000000) (Real.log (919377915047 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (919377915047 / 500000000000) = -Real.log (500000000000 / 919377915047) := by
    rw [show ((919377915047 / 500000000000) : ℝ) = ((500000000000 / 919377915047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (305010297 / 500000000) ≤ -Real.log (50000000000 / 92023465117) ∧
    -Real.log (50000000000 / 92023465117) ≤ (122004119 / 200000000) := by
  have h := checkLog_sound (w := (42023465117 / 142023465117)) (n := 12)
    (lo := (305010297 / 500000000)) (hi := (122004119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92023465117 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92023465117 / 50000000000) = 1/(50000000000 / 92023465117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (305010297 / 500000000) (122004119 / 200000000) (Real.log (92023465117 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (92023465117 / 50000000000) = -Real.log (50000000000 / 92023465117) := by
    rw [show ((92023465117 / 50000000000) : ℝ) = ((50000000000 / 92023465117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (217465439 / 500000000) ≤ -Real.log (500000000000 / 772428136439) ∧
    -Real.log (500000000000 / 772428136439) ≤ (434930879 / 1000000000) := by
  have h := checkLog_sound (w := (272428136439 / 1272428136439)) (n := 12)
    (lo := (217465439 / 500000000)) (hi := (434930879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((772428136439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(772428136439 / 500000000000) = 1/(500000000000 / 772428136439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (217465439 / 500000000) (434930879 / 1000000000) (Real.log (772428136439 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (772428136439 / 500000000000) = -Real.log (500000000000 / 772428136439) := by
    rw [show ((772428136439 / 500000000000) : ℝ) = ((500000000000 / 772428136439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (435610059 / 1000000000) ≤ -Real.log (250000000000 / 386476466283) ∧
    -Real.log (250000000000 / 386476466283) ≤ (21780503 / 50000000) := by
  have h := checkLog_sound (w := (136476466283 / 636476466283)) (n := 12)
    (lo := (435610059 / 1000000000)) (hi := (21780503 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386476466283 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386476466283 / 250000000000) = 1/(250000000000 / 386476466283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (435610059 / 1000000000) (21780503 / 50000000) (Real.log (386476466283 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (386476466283 / 250000000000) = -Real.log (250000000000 / 386476466283) := by
    rw [show ((386476466283 / 250000000000) : ℝ) = ((250000000000 / 386476466283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0448
