import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell143
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

theorem reflection_log_1_neg : (288463017 / 1000000000) ≤ -Real.log (320 / 427) ∧
    -Real.log (320 / 427) ≤ (144231509 / 500000000) := by
  have h := checkLog_sound (w := (107 / 747)) (n := 12)
    (lo := (288463017 / 1000000000)) (hi := (144231509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(427 / 320) = 1/(320 / 427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (288463017 / 1000000000) (144231509 / 500000000) (Real.log (427 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (427 / 320) = -Real.log (320 / 427) := by
    rw [show ((427 / 320) : ℝ) = ((320 / 427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (40702883 / 100000000) ≤ -Real.log (213 / 320) ∧
    -Real.log (213 / 320) ≤ (407028831 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 533)) (n := 12)
    (lo := (40702883 / 100000000)) (hi := (407028831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 213) = 1/(213 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-407028831 / 1000000000) (-40702883 / 100000000) (Real.log (213 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (28802381 / 100000000) ≤ -Real.log (5120 / 6829) ∧
    -Real.log (5120 / 6829) ≤ (288023811 / 1000000000) := by
  have h := checkLog_sound (w := (1709 / 11949)) (n := 12)
    (lo := (28802381 / 100000000)) (hi := (288023811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6829 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6829 / 5120) = 1/(5120 / 6829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (28802381 / 100000000) (288023811 / 1000000000) (Real.log (6829 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6829 / 5120) = -Real.log (5120 / 6829) := by
    rw [show ((6829 / 5120) : ℝ) = ((5120 / 6829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (81229787 / 200000000) ≤ -Real.log (3411 / 5120) ∧
    -Real.log (3411 / 5120) ≤ (50768617 / 125000000) := by
  have h := checkLog_sound (w := (1709 / 8531)) (n := 12)
    (lo := (81229787 / 200000000)) (hi := (50768617 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3411) = 1/(3411 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-50768617 / 125000000) (-81229787 / 200000000) (Real.log (3411 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (106414469 / 500000000) ≤ -Real.log (1000000 / 1237173) ∧
    -Real.log (1000000 / 1237173) ≤ (212828939 / 1000000000) := by
  have h := checkLog_sound (w := (237173 / 2237173)) (n := 12)
    (lo := (106414469 / 500000000)) (hi := (212828939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1237173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1237173 / 1000000) = 1/(1000000 / 1237173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (106414469 / 500000000) (212828939 / 1000000000) (Real.log (1237173 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1237173 / 1000000) = -Real.log (1000000 / 1237173) := by
    rw [show ((1237173 / 1000000) : ℝ) = ((1000000 / 1237173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (270724009 / 1000000000) ≤ -Real.log (762827 / 1000000) ∧
    -Real.log (762827 / 1000000) ≤ (27072401 / 100000000) := by
  have h := checkLog_sound (w := (237173 / 1762827)) (n := 12)
    (lo := (270724009 / 1000000000)) (hi := (27072401 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 762827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 762827) = 1/(762827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-27072401 / 100000000) (-270724009 / 1000000000) (Real.log (762827 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10658499 / 50000000) ≤ -Real.log (200000 / 247519) ∧
    -Real.log (200000 / 247519) ≤ (213169981 / 1000000000) := by
  have h := checkLog_sound (w := (47519 / 447519)) (n := 12)
    (lo := (10658499 / 50000000)) (hi := (213169981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247519 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247519 / 200000) = 1/(200000 / 247519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10658499 / 50000000) (213169981 / 1000000000) (Real.log (247519 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (247519 / 200000) = -Real.log (200000 / 247519) := by
    rw [show ((247519 / 200000) : ℝ) = ((200000 / 247519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (33909671 / 125000000) ≤ -Real.log (152481 / 200000) ∧
    -Real.log (152481 / 200000) ≤ (271277369 / 1000000000) := by
  have h := checkLog_sound (w := (47519 / 352481)) (n := 12)
    (lo := (33909671 / 125000000)) (hi := (271277369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 152481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 152481) = 1/(152481 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-271277369 / 1000000000) (-33909671 / 125000000) (Real.log (152481 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (78656551 / 500000000) ≤ -Real.log (500000 / 585181) ∧
    -Real.log (500000 / 585181) ≤ (157313103 / 1000000000) := by
  have h := checkLog_sound (w := (85181 / 1085181)) (n := 12)
    (lo := (78656551 / 500000000)) (hi := (157313103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585181 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585181 / 500000) = 1/(500000 / 585181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (78656551 / 500000000) (157313103 / 1000000000) (Real.log (585181 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (585181 / 500000) = -Real.log (500000 / 585181) := by
    rw [show ((585181 / 500000) : ℝ) = ((500000 / 585181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (186765817 / 1000000000) ≤ -Real.log (414819 / 500000) ∧
    -Real.log (414819 / 500000) ≤ (93382909 / 500000000) := by
  have h := checkLog_sound (w := (85181 / 914819)) (n := 12)
    (lo := (186765817 / 1000000000)) (hi := (93382909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414819) = 1/(414819 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-93382909 / 500000000) (-186765817 / 1000000000) (Real.log (414819 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31516101 / 200000000) ≤ -Real.log (40000 / 46827) ∧
    -Real.log (40000 / 46827) ≤ (78790253 / 500000000) := by
  have h := checkLog_sound (w := (6827 / 86827)) (n := 12)
    (lo := (31516101 / 200000000)) (hi := (78790253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46827 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46827 / 40000) = 1/(40000 / 46827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31516101 / 200000000) (78790253 / 500000000) (Real.log (46827 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (46827 / 40000) = -Real.log (40000 / 46827) := by
    rw [show ((46827 / 40000) : ℝ) = ((40000 / 46827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (93571581 / 500000000) ≤ -Real.log (33173 / 40000) ∧
    -Real.log (33173 / 40000) ≤ (187143163 / 1000000000) := by
  have h := checkLog_sound (w := (6827 / 73173)) (n := 12)
    (lo := (93571581 / 500000000)) (hi := (187143163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 33173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 33173) = 1/(33173 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-187143163 / 1000000000) (-93571581 / 500000000) (Real.log (33173 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (138834549 / 200000000) ≤ -Real.log (100000000000 / 200205218411) ∧
    -Real.log (100000000000 / 200205218411) ≤ (694172747 / 1000000000) := by
  have h := checkLog_sound (w := (205218411 / 400205218411)) (n := 12)
    (lo := (205113 / 200000000)) (hi := (512783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200205218411 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200205218411 / 200000000000) = 1/(100000000000 / 200205218411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (138834549 / 200000000) (694172747 / 1000000000) (Real.log (200205218411 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (200205218411 / 100000000000) = -Real.log (100000000000 / 200205218411) := by
    rw [show ((200205218411 / 100000000000) : ℝ) = ((100000000000 / 200205218411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (347745923 / 500000000) ≤ -Real.log (500000000000 / 1002347417841) ∧
    -Real.log (500000000000 / 1002347417841) ≤ (86936481 / 125000000) := by
  have h := checkLog_sound (w := (2347417841 / 2002347417841)) (n := 12)
    (lo := (1172333 / 500000000)) (hi := (2344667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1002347417841 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1002347417841 / 1000000000000) = 1/(500000000000 / 1002347417841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (347745923 / 500000000) (86936481 / 125000000) (Real.log (1002347417841 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1002347417841 / 500000000000) = -Real.log (500000000000 / 1002347417841) := by
    rw [show ((1002347417841 / 500000000000) : ℝ) = ((500000000000 / 1002347417841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (120888237 / 250000000) ≤ -Real.log (500000000000 / 810913221477) ∧
    -Real.log (500000000000 / 810913221477) ≤ (483552949 / 1000000000) := by
  have h := checkLog_sound (w := (310913221477 / 1310913221477)) (n := 12)
    (lo := (120888237 / 250000000)) (hi := (483552949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((810913221477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(810913221477 / 500000000000) = 1/(500000000000 / 810913221477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (120888237 / 250000000) (483552949 / 1000000000) (Real.log (810913221477 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (810913221477 / 500000000000) = -Real.log (500000000000 / 810913221477) := by
    rw [show ((810913221477 / 500000000000) : ℝ) = ((500000000000 / 810913221477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (121111837 / 250000000) ≤ -Real.log (500000000000 / 811638827133) ∧
    -Real.log (500000000000 / 811638827133) ≤ (484447349 / 1000000000) := by
  have h := checkLog_sound (w := (311638827133 / 1311638827133)) (n := 12)
    (lo := (121111837 / 250000000)) (hi := (484447349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811638827133 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811638827133 / 500000000000) = 1/(500000000000 / 811638827133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (121111837 / 250000000) (484447349 / 1000000000) (Real.log (811638827133 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (811638827133 / 500000000000) = -Real.log (500000000000 / 811638827133) := by
    rw [show ((811638827133 / 500000000000) : ℝ) = ((500000000000 / 811638827133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (8601973 / 25000000) ≤ -Real.log (500000000000 / 705344981787) ∧
    -Real.log (500000000000 / 705344981787) ≤ (344078921 / 1000000000) := by
  have h := checkLog_sound (w := (205344981787 / 1205344981787)) (n := 12)
    (lo := (8601973 / 25000000)) (hi := (344078921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705344981787 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705344981787 / 500000000000) = 1/(500000000000 / 705344981787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (8601973 / 25000000) (344078921 / 1000000000) (Real.log (705344981787 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (705344981787 / 500000000000) = -Real.log (500000000000 / 705344981787) := by
    rw [show ((705344981787 / 500000000000) : ℝ) = ((500000000000 / 705344981787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (344723667 / 1000000000) ≤ -Real.log (125000000000 / 176449974377) ∧
    -Real.log (125000000000 / 176449974377) ≤ (86180917 / 250000000) := by
  have h := checkLog_sound (w := (51449974377 / 301449974377)) (n := 12)
    (lo := (344723667 / 1000000000)) (hi := (86180917 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176449974377 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176449974377 / 125000000000) = 1/(125000000000 / 176449974377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (344723667 / 1000000000) (86180917 / 250000000) (Real.log (176449974377 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (176449974377 / 125000000000) = -Real.log (125000000000 / 176449974377) := by
    rw [show ((176449974377 / 125000000000) : ℝ) = ((125000000000 / 176449974377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (923833 / 31250000) ≤ -Real.log (1553392071 / 1600000000) ∧
    -Real.log (1553392071 / 1600000000) ≤ (29562657 / 1000000000) := by
  have h := checkLog_sound (w := (46607929 / 3153392071)) (n := 12)
    (lo := (923833 / 31250000)) (hi := (29562657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1553392071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1553392071) = 1/(1553392071 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-29562657 / 1000000000) (-923833 / 31250000) (Real.log (1553392071 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5890543 / 200000000) ≤ -Real.log (242744197239 / 250000000000) ∧
    -Real.log (242744197239 / 250000000000) ≤ (7363179 / 250000000) := by
  have h := checkLog_sound (w := (7255802761 / 492744197239)) (n := 12)
    (lo := (5890543 / 200000000)) (hi := (7363179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242744197239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242744197239) = 1/(242744197239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-7363179 / 250000000) (-5890543 / 200000000) (Real.log (242744197239 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell143
