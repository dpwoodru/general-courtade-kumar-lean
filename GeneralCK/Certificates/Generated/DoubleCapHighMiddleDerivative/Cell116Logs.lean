import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell116
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

theorem reflection_log_1_neg : (276536203 / 1000000000) ≤ -Real.log (5120 / 6751) ∧
    -Real.log (5120 / 6751) ≤ (69134051 / 250000000) := by
  have h := checkLog_sound (w := (1631 / 11871)) (n := 12)
    (lo := (276536203 / 1000000000)) (hi := (69134051 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6751 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6751 / 5120) = 1/(5120 / 6751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (276536203 / 1000000000) (69134051 / 250000000) (Real.log (6751 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6751 / 5120) = -Real.log (5120 / 6751) := by
    rw [show ((6751 / 5120) : ℝ) = ((5120 / 6751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (95884819 / 250000000) ≤ -Real.log (3489 / 5120) ∧
    -Real.log (3489 / 5120) ≤ (383539277 / 1000000000) := by
  have h := checkLog_sound (w := (1631 / 8609)) (n := 12)
    (lo := (95884819 / 250000000)) (hi := (383539277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3489) = 1/(3489 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-383539277 / 1000000000) (-95884819 / 250000000) (Real.log (3489 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11043669 / 40000000) ≤ -Real.log (1280 / 1687) ∧
    -Real.log (1280 / 1687) ≤ (138045863 / 500000000) := by
  have h := checkLog_sound (w := (407 / 2967)) (n := 12)
    (lo := (11043669 / 40000000)) (hi := (138045863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1687 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1687 / 1280) = 1/(1280 / 1687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11043669 / 40000000) (138045863 / 500000000) (Real.log (1687 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1687 / 1280) = -Real.log (1280 / 1687) := by
    rw [show ((1687 / 1280) : ℝ) = ((1280 / 1687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (382679801 / 1000000000) ≤ -Real.log (873 / 1280) ∧
    -Real.log (873 / 1280) ≤ (191339901 / 500000000) := by
  have h := checkLog_sound (w := (407 / 2153)) (n := 12)
    (lo := (382679801 / 1000000000)) (hi := (191339901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 873) = 1/(873 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-191339901 / 500000000) (-382679801 / 1000000000) (Real.log (873 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (101807451 / 500000000) ≤ -Real.log (500000 / 612913) ∧
    -Real.log (500000 / 612913) ≤ (203614903 / 1000000000) := by
  have h := checkLog_sound (w := (112913 / 1112913)) (n := 12)
    (lo := (101807451 / 500000000)) (hi := (203614903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612913 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612913 / 500000) = 1/(500000 / 612913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (101807451 / 500000000) (203614903 / 1000000000) (Real.log (612913 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (612913 / 500000) = -Real.log (500000 / 612913) := by
    rw [show ((612913 / 500000) : ℝ) = ((500000 / 612913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (7998707 / 31250000) ≤ -Real.log (387087 / 500000) ∧
    -Real.log (387087 / 500000) ≤ (2047669 / 8000000) := by
  have h := checkLog_sound (w := (112913 / 887087)) (n := 12)
    (lo := (7998707 / 31250000)) (hi := (2047669 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 387087) = 1/(387087 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2047669 / 8000000) (-7998707 / 31250000) (Real.log (387087 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (40791657 / 200000000) ≤ -Real.log (1000000 / 1226247) ∧
    -Real.log (1000000 / 1226247) ≤ (101979143 / 500000000) := by
  have h := checkLog_sound (w := (226247 / 2226247)) (n := 12)
    (lo := (40791657 / 200000000)) (hi := (101979143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1226247 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1226247 / 1000000) = 1/(1000000 / 1226247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (40791657 / 200000000) (101979143 / 500000000) (Real.log (1226247 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1226247 / 1000000) = -Real.log (1000000 / 1226247) := by
    rw [show ((1226247 / 1000000) : ℝ) = ((1000000 / 1226247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (256502577 / 1000000000) ≤ -Real.log (773753 / 1000000) ∧
    -Real.log (773753 / 1000000) ≤ (128251289 / 500000000) := by
  have h := checkLog_sound (w := (226247 / 1773753)) (n := 12)
    (lo := (256502577 / 1000000000)) (hi := (128251289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 773753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 773753) = 1/(773753 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-128251289 / 500000000) (-256502577 / 1000000000) (Real.log (773753 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (150118561 / 1000000000) ≤ -Real.log (250000 / 290493) ∧
    -Real.log (250000 / 290493) ≤ (75059281 / 500000000) := by
  have h := checkLog_sound (w := (40493 / 540493)) (n := 12)
    (lo := (150118561 / 1000000000)) (hi := (75059281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290493 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(290493 / 250000) = 1/(250000 / 290493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (150118561 / 1000000000) (75059281 / 500000000) (Real.log (290493 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (290493 / 250000) = -Real.log (250000 / 290493) := by
    rw [show ((290493 / 250000) : ℝ) = ((250000 / 290493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (88351883 / 500000000) ≤ -Real.log (209507 / 250000) ∧
    -Real.log (209507 / 250000) ≤ (176703767 / 1000000000) := by
  have h := checkLog_sound (w := (40493 / 459507)) (n := 12)
    (lo := (88351883 / 500000000)) (hi := (176703767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 209507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 209507) = 1/(209507 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-176703767 / 1000000000) (-88351883 / 500000000) (Real.log (209507 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (75193087 / 500000000) ≤ -Real.log (1000000 / 1162283) ∧
    -Real.log (1000000 / 1162283) ≤ (6015447 / 40000000) := by
  have h := checkLog_sound (w := (162283 / 2162283)) (n := 12)
    (lo := (75193087 / 500000000)) (hi := (6015447 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1162283 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1162283 / 1000000) = 1/(1000000 / 1162283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (75193087 / 500000000) (6015447 / 40000000) (Real.log (1162283 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1162283 / 1000000) = -Real.log (1000000 / 1162283) := by
    rw [show ((1162283 / 1000000) : ℝ) = ((1000000 / 1162283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (691699 / 3906250) ≤ -Real.log (837717 / 1000000) ∧
    -Real.log (837717 / 1000000) ≤ (35414989 / 200000000) := by
  have h := checkLog_sound (w := (162283 / 1837717)) (n := 12)
    (lo := (691699 / 3906250)) (hi := (35414989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 837717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 837717) = 1/(837717 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-35414989 / 200000000) (-691699 / 3906250) (Real.log (837717 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (329385763 / 500000000) ≤ -Real.log (500000000000 / 966208476517) ∧
    -Real.log (500000000000 / 966208476517) ≤ (658771527 / 1000000000) := by
  have h := checkLog_sound (w := (466208476517 / 1466208476517)) (n := 12)
    (lo := (329385763 / 500000000)) (hi := (658771527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((966208476517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(966208476517 / 500000000000) = 1/(500000000000 / 966208476517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (329385763 / 500000000) (658771527 / 1000000000) (Real.log (966208476517 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (966208476517 / 500000000000) = -Real.log (500000000000 / 966208476517) := by
    rw [show ((966208476517 / 500000000000) : ℝ) = ((500000000000 / 966208476517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (660075479 / 1000000000) ≤ -Real.log (6250000000 / 12093364861) ∧
    -Real.log (6250000000 / 12093364861) ≤ (16501887 / 25000000) := by
  have h := checkLog_sound (w := (5843364861 / 18343364861)) (n := 12)
    (lo := (660075479 / 1000000000)) (hi := (16501887 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12093364861 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12093364861 / 6250000000) = 1/(6250000000 / 12093364861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (660075479 / 1000000000) (16501887 / 25000000) (Real.log (12093364861 / 6250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (12093364861 / 6250000000) = -Real.log (6250000000 / 12093364861) := by
    rw [show ((12093364861 / 6250000000) : ℝ) = ((6250000000 / 12093364861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (229786763 / 500000000) ≤ -Real.log (500000000000 / 791699282073) ∧
    -Real.log (500000000000 / 791699282073) ≤ (459573527 / 1000000000) := by
  have h := checkLog_sound (w := (291699282073 / 1291699282073)) (n := 12)
    (lo := (229786763 / 500000000)) (hi := (459573527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791699282073 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791699282073 / 500000000000) = 1/(500000000000 / 791699282073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (229786763 / 500000000) (459573527 / 1000000000) (Real.log (791699282073 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (791699282073 / 500000000000) = -Real.log (500000000000 / 791699282073) := by
    rw [show ((791699282073 / 500000000000) : ℝ) = ((500000000000 / 791699282073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (460460863 / 1000000000) ≤ -Real.log (500000000000 / 792402097311) ∧
    -Real.log (500000000000 / 792402097311) ≤ (7194701 / 15625000) := by
  have h := checkLog_sound (w := (292402097311 / 1292402097311)) (n := 12)
    (lo := (460460863 / 1000000000)) (hi := (7194701 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792402097311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792402097311 / 500000000000) = 1/(500000000000 / 792402097311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (460460863 / 1000000000) (7194701 / 15625000) (Real.log (792402097311 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (792402097311 / 500000000000) = -Real.log (500000000000 / 792402097311) := by
    rw [show ((792402097311 / 500000000000) : ℝ) = ((500000000000 / 792402097311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (326822327 / 1000000000) ≤ -Real.log (100000000000 / 138655510317) ∧
    -Real.log (100000000000 / 138655510317) ≤ (40852791 / 125000000) := by
  have h := checkLog_sound (w := (38655510317 / 238655510317)) (n := 12)
    (lo := (326822327 / 1000000000)) (hi := (40852791 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138655510317 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138655510317 / 100000000000) = 1/(100000000000 / 138655510317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (326822327 / 1000000000) (40852791 / 125000000) (Real.log (138655510317 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (138655510317 / 100000000000) = -Real.log (100000000000 / 138655510317) := by
    rw [show ((138655510317 / 100000000000) : ℝ) = ((100000000000 / 138655510317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (163730559 / 500000000) ≤ -Real.log (500000000000 / 693720552407) ∧
    -Real.log (500000000000 / 693720552407) ≤ (327461119 / 1000000000) := by
  have h := checkLog_sound (w := (193720552407 / 1193720552407)) (n := 12)
    (lo := (163730559 / 500000000)) (hi := (327461119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693720552407 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693720552407 / 500000000000) = 1/(500000000000 / 693720552407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (163730559 / 500000000) (327461119 / 1000000000) (Real.log (693720552407 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (693720552407 / 500000000000) = -Real.log (500000000000 / 693720552407) := by
    rw [show ((693720552407 / 500000000000) : ℝ) = ((500000000000 / 693720552407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (26688769 / 1000000000) ≤ -Real.log (973664227911 / 1000000000000) ∧
    -Real.log (973664227911 / 1000000000000) ≤ (2668877 / 100000000) := by
  have h := checkLog_sound (w := (26335772089 / 1973664227911)) (n := 12)
    (lo := (26688769 / 1000000000)) (hi := (2668877 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973664227911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973664227911) = 1/(973664227911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2668877 / 100000000) (-26688769 / 1000000000) (Real.log (973664227911 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6646301 / 250000000) ≤ -Real.log (60860316951 / 62500000000) ∧
    -Real.log (60860316951 / 62500000000) ≤ (5317041 / 200000000) := by
  have h := checkLog_sound (w := (1639683049 / 123360316951)) (n := 12)
    (lo := (6646301 / 250000000)) (hi := (5317041 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60860316951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60860316951) = 1/(60860316951 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5317041 / 200000000) (-6646301 / 250000000) (Real.log (60860316951 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell116
