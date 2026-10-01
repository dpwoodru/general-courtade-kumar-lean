import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0379
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

theorem reflection_log_1_neg : (205250037 / 1000000000) ≤ -Real.log (10240 / 12573) ∧
    -Real.log (10240 / 12573) ≤ (102625019 / 500000000) := by
  have h := checkLog_sound (w := (2333 / 22813)) (n := 12)
    (lo := (205250037 / 1000000000)) (hi := (102625019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12573 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12573 / 10240) = 1/(10240 / 12573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (205250037 / 1000000000) (102625019 / 500000000) (Real.log (12573 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12573 / 10240) = -Real.log (10240 / 12573) := by
    rw [show ((12573 / 10240) : ℝ) = ((10240 / 12573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (32319147 / 125000000) ≤ -Real.log (7907 / 10240) ∧
    -Real.log (7907 / 10240) ≤ (258553177 / 1000000000) := by
  have h := checkLog_sound (w := (2333 / 18147)) (n := 12)
    (lo := (32319147 / 125000000)) (hi := (258553177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7907) = 1/(7907 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-258553177 / 1000000000) (-32319147 / 125000000) (Real.log (7907 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (102505701 / 500000000) ≤ -Real.log (1024 / 1257) ∧
    -Real.log (1024 / 1257) ≤ (205011403 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 2281)) (n := 12)
    (lo := (102505701 / 500000000)) (hi := (205011403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1257 / 1024) = 1/(1024 / 1257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (102505701 / 500000000) (205011403 / 1000000000) (Real.log (1257 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1257 / 1024) = -Real.log (1024 / 1257) := by
    rw [show ((1257 / 1024) : ℝ) = ((1024 / 1257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (258173837 / 1000000000) ≤ -Real.log (791 / 1024) ∧
    -Real.log (791 / 1024) ≤ (129086919 / 500000000) := by
  have h := checkLog_sound (w := (233 / 1815)) (n := 12)
    (lo := (258173837 / 1000000000)) (hi := (129086919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 791) = 1/(791 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-129086919 / 500000000) (-258173837 / 1000000000) (Real.log (791 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (93865549 / 250000000) ≤ -Real.log (5120 / 7453) ∧
    -Real.log (5120 / 7453) ≤ (375462197 / 1000000000) := by
  have h := checkLog_sound (w := (2333 / 12573)) (n := 12)
    (lo := (93865549 / 250000000)) (hi := (375462197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7453 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7453 / 5120) = 1/(5120 / 7453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (93865549 / 250000000) (375462197 / 1000000000) (Real.log (7453 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7453 / 5120) = -Real.log (5120 / 7453) := by
    rw [show ((7453 / 5120) : ℝ) = ((5120 / 7453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (60818869 / 100000000) ≤ -Real.log (2787 / 5120) ∧
    -Real.log (2787 / 5120) ≤ (608188691 / 1000000000) := by
  have h := checkLog_sound (w := (2333 / 7907)) (n := 12)
    (lo := (60818869 / 100000000)) (hi := (608188691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2787) = 1/(2787 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-608188691 / 1000000000) (-60818869 / 100000000) (Real.log (2787 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (375059593 / 1000000000) ≤ -Real.log (512 / 745) ∧
    -Real.log (512 / 745) ≤ (187529797 / 500000000) := by
  have h := checkLog_sound (w := (233 / 1257)) (n := 12)
    (lo := (375059593 / 1000000000)) (hi := (187529797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745 / 512) = 1/(512 / 745) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (375059593 / 1000000000) (187529797 / 500000000) (Real.log (745 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (745 / 512) = -Real.log (512 / 745) := by
    rw [show ((745 / 512) : ℝ) = ((512 / 745) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (607112843 / 1000000000) ≤ -Real.log (279 / 512) ∧
    -Real.log (279 / 512) ≤ (151778211 / 250000000) := by
  have h := checkLog_sound (w := (233 / 791)) (n := 12)
    (lo := (607112843 / 1000000000)) (hi := (151778211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 279) = 1/(279 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-151778211 / 250000000) (-607112843 / 1000000000) (Real.log (279 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (549389 / 1953125) ≤ -Real.log (500000 / 662417) ∧
    -Real.log (500000 / 662417) ≤ (281287169 / 1000000000) := by
  have h := checkLog_sound (w := (162417 / 1162417)) (n := 12)
    (lo := (549389 / 1953125)) (hi := (281287169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((662417 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(662417 / 500000) = 1/(500000 / 662417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (549389 / 1953125) (281287169 / 1000000000) (Real.log (662417 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (662417 / 500000) = -Real.log (500000 / 662417) := by
    rw [show ((662417 / 500000) : ℝ) = ((500000 / 662417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (98199173 / 250000000) ≤ -Real.log (337583 / 500000) ∧
    -Real.log (337583 / 500000) ≤ (392796693 / 1000000000) := by
  have h := checkLog_sound (w := (162417 / 837583)) (n := 12)
    (lo := (98199173 / 250000000)) (hi := (392796693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 337583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 337583) = 1/(337583 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-392796693 / 1000000000) (-98199173 / 250000000) (Real.log (337583 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (11264407 / 40000000) ≤ -Real.log (500000 / 662631) ∧
    -Real.log (500000 / 662631) ≤ (4400159 / 15625000) := by
  have h := checkLog_sound (w := (162631 / 1162631)) (n := 12)
    (lo := (11264407 / 40000000)) (hi := (4400159 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((662631 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(662631 / 500000) = 1/(500000 / 662631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (11264407 / 40000000) (4400159 / 15625000) (Real.log (662631 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (662631 / 500000) = -Real.log (500000 / 662631) := by
    rw [show ((662631 / 500000) : ℝ) = ((500000 / 662631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (393430811 / 1000000000) ≤ -Real.log (337369 / 500000) ∧
    -Real.log (337369 / 500000) ≤ (98357703 / 250000000) := by
  have h := checkLog_sound (w := (162631 / 837369)) (n := 12)
    (lo := (393430811 / 1000000000)) (hi := (98357703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 337369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 337369) = 1/(337369 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-98357703 / 250000000) (-393430811 / 1000000000) (Real.log (337369 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (42473459 / 200000000) ≤ -Real.log (500000 / 618301) ∧
    -Real.log (500000 / 618301) ≤ (3318239 / 15625000) := by
  have h := checkLog_sound (w := (118301 / 1118301)) (n := 12)
    (lo := (42473459 / 200000000)) (hi := (3318239 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618301 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618301 / 500000) = 1/(500000 / 618301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (42473459 / 200000000) (3318239 / 15625000) (Real.log (618301 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (618301 / 500000) = -Real.log (500000 / 618301) := by
    rw [show ((618301 / 500000) : ℝ) = ((500000 / 618301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (134987879 / 500000000) ≤ -Real.log (381699 / 500000) ∧
    -Real.log (381699 / 500000) ≤ (269975759 / 1000000000) := by
  have h := checkLog_sound (w := (118301 / 881699)) (n := 12)
    (lo := (134987879 / 500000000)) (hi := (269975759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 381699) = 1/(381699 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-269975759 / 1000000000) (-134987879 / 500000000) (Real.log (381699 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (13289683 / 62500000) ≤ -Real.log (1000000 / 1236933) ∧
    -Real.log (1000000 / 1236933) ≤ (212634929 / 1000000000) := by
  have h := checkLog_sound (w := (236933 / 2236933)) (n := 12)
    (lo := (13289683 / 62500000)) (hi := (212634929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1236933 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1236933 / 1000000) = 1/(1000000 / 1236933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (13289683 / 62500000) (212634929 / 1000000000) (Real.log (1236933 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1236933 / 1000000) = -Real.log (1000000 / 1236933) := by
    rw [show ((1236933 / 1000000) : ℝ) = ((1000000 / 1236933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1690059 / 6250000) ≤ -Real.log (763067 / 1000000) ∧
    -Real.log (763067 / 1000000) ≤ (270409441 / 1000000000) := by
  have h := checkLog_sound (w := (236933 / 1763067)) (n := 12)
    (lo := (1690059 / 6250000)) (hi := (270409441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 763067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 763067) = 1/(763067 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-270409441 / 1000000000) (-1690059 / 6250000) (Real.log (763067 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (33704193 / 50000000) ≤ -Real.log (500000000000 / 981117236353) ∧
    -Real.log (500000000000 / 981117236353) ≤ (674083861 / 1000000000) := by
  have h := checkLog_sound (w := (481117236353 / 1481117236353)) (n := 12)
    (lo := (33704193 / 50000000)) (hi := (674083861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981117236353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981117236353 / 500000000000) = 1/(500000000000 / 981117236353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (33704193 / 50000000) (674083861 / 1000000000) (Real.log (981117236353 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (981117236353 / 500000000000) = -Real.log (500000000000 / 981117236353) := by
    rw [show ((981117236353 / 500000000000) : ℝ) = ((500000000000 / 981117236353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (675040987 / 1000000000) ≤ -Real.log (500000000000 / 982056739061) ∧
    -Real.log (500000000000 / 982056739061) ≤ (168760247 / 250000000) := by
  have h := checkLog_sound (w := (482056739061 / 1482056739061)) (n := 12)
    (lo := (675040987 / 1000000000)) (hi := (168760247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982056739061 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982056739061 / 500000000000) = 1/(500000000000 / 982056739061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (675040987 / 1000000000) (168760247 / 250000000) (Real.log (982056739061 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (982056739061 / 500000000000) = -Real.log (500000000000 / 982056739061) := by
    rw [show ((982056739061 / 500000000000) : ℝ) = ((500000000000 / 982056739061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (241171527 / 500000000) ≤ -Real.log (250000000000 / 404966347829) ∧
    -Real.log (250000000000 / 404966347829) ≤ (96468611 / 200000000) := by
  have h := checkLog_sound (w := (154966347829 / 654966347829)) (n := 12)
    (lo := (241171527 / 500000000)) (hi := (96468611 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((404966347829 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(404966347829 / 250000000000) = 1/(250000000000 / 404966347829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (241171527 / 500000000) (96468611 / 200000000) (Real.log (404966347829 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (404966347829 / 250000000000) = -Real.log (250000000000 / 404966347829) := by
    rw [show ((404966347829 / 250000000000) : ℝ) = ((250000000000 / 404966347829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (30190273 / 62500000) ≤ -Real.log (125000000000 / 202625228191) ∧
    -Real.log (125000000000 / 202625228191) ≤ (483044369 / 1000000000) := by
  have h := checkLog_sound (w := (77625228191 / 327625228191)) (n := 12)
    (lo := (30190273 / 62500000)) (hi := (483044369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202625228191 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202625228191 / 125000000000) = 1/(125000000000 / 202625228191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (30190273 / 62500000) (483044369 / 1000000000) (Real.log (202625228191 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (202625228191 / 125000000000) = -Real.log (125000000000 / 202625228191) := by
    rw [show ((202625228191 / 125000000000) : ℝ) = ((125000000000 / 202625228191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0379
