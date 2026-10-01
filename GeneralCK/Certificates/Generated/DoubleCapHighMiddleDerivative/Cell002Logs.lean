import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell002
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

theorem reflection_log_1_neg : (224548813 / 1000000000) ≤ -Real.log (5120 / 6409) ∧
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


theorem reflection_log_1 : Bounds (224548813 / 1000000000) (112274407 / 500000000) (Real.log (6409 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6409 / 5120) = -Real.log (5120 / 6409) := by
    rw [show ((6409 / 5120) : ℝ) = ((5120 / 6409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (290028573 / 1000000000) ≤ -Real.log (3831 / 5120) ∧
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


theorem reflection_log_2 : Bounds (-145014287 / 500000000) (-290028573 / 1000000000) (Real.log (3831 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (56020153 / 250000000) ≤ -Real.log (2560 / 3203) ∧
    -Real.log (2560 / 3203) ≤ (224080613 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 5763)) (n := 12)
    (lo := (56020153 / 250000000)) (hi := (224080613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3203 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3203 / 2560) = 1/(2560 / 3203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (56020153 / 250000000) (224080613 / 1000000000) (Real.log (3203 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3203 / 2560) = -Real.log (2560 / 3203) := by
    rw [show ((3203 / 2560) : ℝ) = ((2560 / 3203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (144622897 / 500000000) ≤ -Real.log (1917 / 2560) ∧
    -Real.log (1917 / 2560) ≤ (57849159 / 200000000) := by
  have h := checkLog_sound (w := (643 / 4477)) (n := 12)
    (lo := (144622897 / 500000000)) (hi := (57849159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1917) = 1/(1917 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-57849159 / 200000000) (-144622897 / 500000000) (Real.log (1917 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (163889389 / 1000000000) ≤ -Real.log (250000 / 294521) ∧
    -Real.log (250000 / 294521) ≤ (16388939 / 100000000) := by
  have h := checkLog_sound (w := (44521 / 544521)) (n := 12)
    (lo := (163889389 / 1000000000)) (hi := (16388939 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294521 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294521 / 250000) = 1/(250000 / 294521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (163889389 / 1000000000) (16388939 / 100000000) (Real.log (294521 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (294521 / 250000) = -Real.log (250000 / 294521) := by
    rw [show ((294521 / 250000) : ℝ) = ((250000 / 294521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (98058539 / 500000000) ≤ -Real.log (205479 / 250000) ∧
    -Real.log (205479 / 250000) ≤ (196117079 / 1000000000) := by
  have h := checkLog_sound (w := (44521 / 455479)) (n := 12)
    (lo := (98058539 / 500000000)) (hi := (196117079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 205479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 205479) = 1/(205479 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-196117079 / 1000000000) (-98058539 / 500000000) (Real.log (205479 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41061247 / 250000000) ≤ -Real.log (1000000 / 1178503) ∧
    -Real.log (1000000 / 1178503) ≤ (164244989 / 1000000000) := by
  have h := checkLog_sound (w := (178503 / 2178503)) (n := 12)
    (lo := (41061247 / 250000000)) (hi := (164244989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1178503 / 1000000) = 1/(1000000 / 1178503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41061247 / 250000000) (164244989 / 1000000000) (Real.log (1178503 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1178503 / 1000000) = -Real.log (1000000 / 1178503) := by
    rw [show ((1178503 / 1000000) : ℝ) = ((1000000 / 1178503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (196626993 / 1000000000) ≤ -Real.log (821497 / 1000000) ∧
    -Real.log (821497 / 1000000) ≤ (98313497 / 500000000) := by
  have h := checkLog_sound (w := (178503 / 1821497)) (n := 12)
    (lo := (196626993 / 1000000000)) (hi := (98313497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 821497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 821497) = 1/(821497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-98313497 / 500000000) (-196626993 / 1000000000) (Real.log (821497 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (59797807 / 500000000) ≤ -Real.log (1000000 / 1127041) ∧
    -Real.log (1000000 / 1127041) ≤ (23919123 / 200000000) := by
  have h := checkLog_sound (w := (127041 / 2127041)) (n := 12)
    (lo := (59797807 / 500000000)) (hi := (23919123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1127041 / 1000000) = 1/(1000000 / 1127041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (59797807 / 500000000) (23919123 / 200000000) (Real.log (1127041 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1127041 / 1000000) = -Real.log (1000000 / 1127041) := by
    rw [show ((1127041 / 1000000) : ℝ) = ((1000000 / 1127041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2122917 / 15625000) ≤ -Real.log (872959 / 1000000) ∧
    -Real.log (872959 / 1000000) ≤ (135866689 / 1000000000) := by
  have h := checkLog_sound (w := (127041 / 1872959)) (n := 12)
    (lo := (2122917 / 15625000)) (hi := (135866689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 872959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 872959) = 1/(872959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-135866689 / 1000000000) (-2122917 / 15625000) (Real.log (872959 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (119866197 / 1000000000) ≤ -Real.log (500000 / 563673) ∧
    -Real.log (500000 / 563673) ≤ (59933099 / 500000000) := by
  have h := checkLog_sound (w := (63673 / 1063673)) (n := 12)
    (lo := (119866197 / 1000000000)) (hi := (59933099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((563673 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(563673 / 500000) = 1/(500000 / 563673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (119866197 / 1000000000) (59933099 / 500000000) (Real.log (563673 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (563673 / 500000) = -Real.log (500000 / 563673) := by
    rw [show ((563673 / 500000) : ℝ) = ((500000 / 563673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (17027017 / 125000000) ≤ -Real.log (436327 / 500000) ∧
    -Real.log (436327 / 500000) ≤ (136216137 / 1000000000) := by
  have h := checkLog_sound (w := (63673 / 936327)) (n := 12)
    (lo := (17027017 / 125000000)) (hi := (136216137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 436327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 436327) = 1/(436327 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-136216137 / 1000000000) (-17027017 / 125000000) (Real.log (436327 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (256663203 / 500000000) ≤ -Real.log (500000000000 / 835419926969) ∧
    -Real.log (500000000000 / 835419926969) ≤ (513326407 / 1000000000) := by
  have h := checkLog_sound (w := (335419926969 / 1335419926969)) (n := 12)
    (lo := (256663203 / 500000000)) (hi := (513326407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((835419926969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(835419926969 / 500000000000) = 1/(500000000000 / 835419926969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (256663203 / 500000000) (513326407 / 1000000000) (Real.log (835419926969 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (835419926969 / 500000000000) = -Real.log (500000000000 / 835419926969) := by
    rw [show ((835419926969 / 500000000000) : ℝ) = ((500000000000 / 835419926969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (257288693 / 500000000) ≤ -Real.log (500000000000 / 836465674759) ∧
    -Real.log (500000000000 / 836465674759) ≤ (514577387 / 1000000000) := by
  have h := checkLog_sound (w := (336465674759 / 1336465674759)) (n := 12)
    (lo := (257288693 / 500000000)) (hi := (514577387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((836465674759 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(836465674759 / 500000000000) = 1/(500000000000 / 836465674759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (257288693 / 500000000) (514577387 / 1000000000) (Real.log (836465674759 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (836465674759 / 500000000000) = -Real.log (500000000000 / 836465674759) := by
    rw [show ((836465674759 / 500000000000) : ℝ) = ((500000000000 / 836465674759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (90001617 / 250000000) ≤ -Real.log (500000000000 / 716669343339) ∧
    -Real.log (500000000000 / 716669343339) ≤ (360006469 / 1000000000) := by
  have h := checkLog_sound (w := (216669343339 / 1216669343339)) (n := 12)
    (lo := (90001617 / 250000000)) (hi := (360006469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716669343339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716669343339 / 500000000000) = 1/(500000000000 / 716669343339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (90001617 / 250000000) (360006469 / 1000000000) (Real.log (716669343339 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (716669343339 / 500000000000) = -Real.log (500000000000 / 716669343339) := by
    rw [show ((716669343339 / 500000000000) : ℝ) = ((500000000000 / 716669343339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (180435991 / 500000000) ≤ -Real.log (500000000000 / 717289898807) ∧
    -Real.log (500000000000 / 717289898807) ≤ (360871983 / 1000000000) := by
  have h := checkLog_sound (w := (217289898807 / 1217289898807)) (n := 12)
    (lo := (180435991 / 500000000)) (hi := (360871983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717289898807 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717289898807 / 500000000000) = 1/(500000000000 / 717289898807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (180435991 / 500000000) (360871983 / 1000000000) (Real.log (717289898807 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (717289898807 / 500000000000) = -Real.log (500000000000 / 717289898807) := by
    rw [show ((717289898807 / 500000000000) : ℝ) = ((500000000000 / 717289898807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (127731151 / 500000000) ≤ -Real.log (500000000000 / 645529171473) ∧
    -Real.log (500000000000 / 645529171473) ≤ (255462303 / 1000000000) := by
  have h := checkLog_sound (w := (145529171473 / 1145529171473)) (n := 12)
    (lo := (127731151 / 500000000)) (hi := (255462303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((645529171473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(645529171473 / 500000000000) = 1/(500000000000 / 645529171473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (127731151 / 500000000) (255462303 / 1000000000) (Real.log (645529171473 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (645529171473 / 500000000000) = -Real.log (500000000000 / 645529171473) := by
    rw [show ((645529171473 / 500000000000) : ℝ) = ((500000000000 / 645529171473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (256082333 / 1000000000) ≤ -Real.log (125000000000 / 161482385917) ∧
    -Real.log (125000000000 / 161482385917) ≤ (128041167 / 500000000) := by
  have h := checkLog_sound (w := (36482385917 / 286482385917)) (n := 12)
    (lo := (256082333 / 1000000000)) (hi := (128041167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161482385917 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161482385917 / 125000000000) = 1/(125000000000 / 161482385917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (256082333 / 1000000000) (128041167 / 500000000) (Real.log (161482385917 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (161482385917 / 125000000000) = -Real.log (125000000000 / 161482385917) := by
    rw [show ((161482385917 / 125000000000) : ℝ) = ((125000000000 / 161482385917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8174969 / 500000000) ≤ -Real.log (245945749071 / 250000000000) ∧
    -Real.log (245945749071 / 250000000000) ≤ (16349939 / 1000000000) := by
  have h := checkLog_sound (w := (4054250929 / 495945749071)) (n := 12)
    (lo := (8174969 / 500000000)) (hi := (16349939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245945749071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245945749071) = 1/(245945749071 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16349939 / 1000000000) (-8174969 / 500000000) (Real.log (245945749071 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8135537 / 500000000) ≤ -Real.log (983860584319 / 1000000000000) ∧
    -Real.log (983860584319 / 1000000000000) ≤ (650843 / 40000000) := by
  have h := checkLog_sound (w := (16139415681 / 1983860584319)) (n := 12)
    (lo := (8135537 / 500000000)) (hi := (650843 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983860584319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983860584319) = 1/(983860584319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-650843 / 40000000) (-8135537 / 500000000) (Real.log (983860584319 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell002
