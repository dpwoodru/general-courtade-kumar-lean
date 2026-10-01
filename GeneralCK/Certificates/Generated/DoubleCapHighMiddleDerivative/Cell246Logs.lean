import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell246
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

theorem reflection_log_1_neg : (332698383 / 1000000000) ≤ -Real.log (5120 / 7141) ∧
    -Real.log (5120 / 7141) ≤ (20793649 / 62500000) := by
  have h := checkLog_sound (w := (2021 / 12261)) (n := 12)
    (lo := (332698383 / 1000000000)) (hi := (20793649 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7141 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7141 / 5120) = 1/(5120 / 7141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (332698383 / 1000000000) (20793649 / 62500000) (Real.log (7141 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7141 / 5120) = -Real.log (5120 / 7141) := by
    rw [show ((7141 / 5120) : ℝ) = ((5120 / 7141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (6275937 / 12500000) ≤ -Real.log (3099 / 5120) ∧
    -Real.log (3099 / 5120) ≤ (502074961 / 1000000000) := by
  have h := checkLog_sound (w := (2021 / 8219)) (n := 12)
    (lo := (6275937 / 12500000)) (hi := (502074961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3099) = 1/(3099 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-502074961 / 1000000000) (-6275937 / 12500000) (Real.log (3099 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (166139093 / 500000000) ≤ -Real.log (2560 / 3569) ∧
    -Real.log (2560 / 3569) ≤ (332278187 / 1000000000) := by
  have h := checkLog_sound (w := (1009 / 6129)) (n := 12)
    (lo := (166139093 / 500000000)) (hi := (332278187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3569 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3569 / 2560) = 1/(2560 / 3569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (166139093 / 500000000) (332278187 / 1000000000) (Real.log (3569 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3569 / 2560) = -Real.log (2560 / 3569) := by
    rw [show ((3569 / 2560) : ℝ) = ((2560 / 3569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (250553687 / 500000000) ≤ -Real.log (1551 / 2560) ∧
    -Real.log (1551 / 2560) ≤ (4008859 / 8000000) := by
  have h := checkLog_sound (w := (1009 / 4111)) (n := 12)
    (lo := (250553687 / 500000000)) (hi := (4008859 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1551) = 1/(1551 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-4008859 / 8000000) (-250553687 / 500000000) (Real.log (1551 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (15459509 / 62500000) ≤ -Real.log (100000 / 128063) ∧
    -Real.log (100000 / 128063) ≤ (49470429 / 200000000) := by
  have h := checkLog_sound (w := (28063 / 228063)) (n := 12)
    (lo := (15459509 / 62500000)) (hi := (49470429 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128063 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128063 / 100000) = 1/(100000 / 128063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (15459509 / 62500000) (49470429 / 200000000) (Real.log (128063 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (128063 / 100000) = -Real.log (100000 / 128063) := by
    rw [show ((128063 / 100000) : ℝ) = ((100000 / 128063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6587589 / 20000000) ≤ -Real.log (71937 / 100000) ∧
    -Real.log (71937 / 100000) ≤ (329379451 / 1000000000) := by
  have h := checkLog_sound (w := (28063 / 171937)) (n := 12)
    (lo := (6587589 / 20000000)) (hi := (329379451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 71937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 71937) = 1/(71937 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-329379451 / 1000000000) (-6587589 / 20000000) (Real.log (71937 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (30960397 / 125000000) ≤ -Real.log (500000 / 640527) ∧
    -Real.log (500000 / 640527) ≤ (247683177 / 1000000000) := by
  have h := checkLog_sound (w := (140527 / 1140527)) (n := 12)
    (lo := (30960397 / 125000000)) (hi := (247683177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640527 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640527 / 500000) = 1/(500000 / 640527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (30960397 / 125000000) (247683177 / 1000000000) (Real.log (640527 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (640527 / 500000) = -Real.log (500000 / 640527) := by
    rw [show ((640527 / 500000) : ℝ) = ((500000 / 640527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (82492257 / 250000000) ≤ -Real.log (359473 / 500000) ∧
    -Real.log (359473 / 500000) ≤ (329969029 / 1000000000) := by
  have h := checkLog_sound (w := (140527 / 859473)) (n := 12)
    (lo := (82492257 / 250000000)) (hi := (329969029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 359473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 359473) = 1/(359473 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-329969029 / 1000000000) (-82492257 / 250000000) (Real.log (359473 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (184701223 / 1000000000) ≤ -Real.log (1000000 / 1202859) ∧
    -Real.log (1000000 / 1202859) ≤ (23087653 / 125000000) := by
  have h := checkLog_sound (w := (202859 / 2202859)) (n := 12)
    (lo := (184701223 / 1000000000)) (hi := (23087653 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1202859 / 1000000) = 1/(1000000 / 1202859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (184701223 / 1000000000) (23087653 / 125000000) (Real.log (1202859 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1202859 / 1000000) = -Real.log (1000000 / 1202859) := by
    rw [show ((1202859 / 1000000) : ℝ) = ((1000000 / 1202859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (113361851 / 500000000) ≤ -Real.log (797141 / 1000000) ∧
    -Real.log (797141 / 1000000) ≤ (226723703 / 1000000000) := by
  have h := checkLog_sound (w := (202859 / 1797141)) (n := 12)
    (lo := (113361851 / 500000000)) (hi := (226723703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 797141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 797141) = 1/(797141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-226723703 / 1000000000) (-113361851 / 500000000) (Real.log (797141 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (184968051 / 1000000000) ≤ -Real.log (50000 / 60159) ∧
    -Real.log (50000 / 60159) ≤ (46242013 / 250000000) := by
  have h := checkLog_sound (w := (10159 / 110159)) (n := 12)
    (lo := (184968051 / 1000000000)) (hi := (46242013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60159 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60159 / 50000) = 1/(50000 / 60159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (184968051 / 1000000000) (46242013 / 250000000) (Real.log (60159 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60159 / 50000) = -Real.log (50000 / 60159) := by
    rw [show ((60159 / 50000) : ℝ) = ((50000 / 60159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (28390809 / 125000000) ≤ -Real.log (39841 / 50000) ∧
    -Real.log (39841 / 50000) ≤ (227126473 / 1000000000) := by
  have h := checkLog_sound (w := (10159 / 89841)) (n := 12)
    (lo := (28390809 / 125000000)) (hi := (227126473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39841) = 1/(39841 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-227126473 / 1000000000) (-28390809 / 125000000) (Real.log (39841 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (833385559 / 1000000000) ≤ -Real.log (250000000000 / 575274016763) ∧
    -Real.log (250000000000 / 575274016763) ≤ (833385561 / 1000000000) := by
  have h := checkLog_sound (w := (75274016763 / 1075274016763)) (n := 12)
    (lo := (140238379 / 1000000000)) (hi := (7011919 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((575274016763 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(575274016763 / 500000000000) = 1/(250000000000 / 575274016763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (833385559 / 1000000000) (833385561 / 1000000000) (Real.log (575274016763 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (575274016763 / 250000000000) = -Real.log (250000000000 / 575274016763) := by
    rw [show ((575274016763 / 250000000000) : ℝ) = ((250000000000 / 575274016763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (834773343 / 1000000000) ≤ -Real.log (250000000000 / 576072926751) ∧
    -Real.log (250000000000 / 576072926751) ≤ (166954669 / 200000000) := by
  have h := checkLog_sound (w := (76072926751 / 1076072926751)) (n := 12)
    (lo := (141626163 / 1000000000)) (hi := (35406541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576072926751 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(576072926751 / 500000000000) = 1/(250000000000 / 576072926751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (834773343 / 1000000000) (166954669 / 200000000) (Real.log (576072926751 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (576072926751 / 250000000000) = -Real.log (250000000000 / 576072926751) := by
    rw [show ((576072926751 / 250000000000) : ℝ) = ((250000000000 / 576072926751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (288365797 / 500000000) ≤ -Real.log (100000000000 / 178021046193) ∧
    -Real.log (100000000000 / 178021046193) ≤ (115346319 / 200000000) := by
  have h := checkLog_sound (w := (78021046193 / 278021046193)) (n := 12)
    (lo := (288365797 / 500000000)) (hi := (115346319 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178021046193 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178021046193 / 100000000000) = 1/(100000000000 / 178021046193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (288365797 / 500000000) (115346319 / 200000000) (Real.log (178021046193 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (178021046193 / 100000000000) = -Real.log (100000000000 / 178021046193) := by
    rw [show ((178021046193 / 100000000000) : ℝ) = ((100000000000 / 178021046193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (144413051 / 250000000) ≤ -Real.log (500000000000 / 890925048613) ∧
    -Real.log (500000000000 / 890925048613) ≤ (115530441 / 200000000) := by
  have h := checkLog_sound (w := (390925048613 / 1390925048613)) (n := 12)
    (lo := (144413051 / 250000000)) (hi := (115530441 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((890925048613 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(890925048613 / 500000000000) = 1/(500000000000 / 890925048613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (144413051 / 250000000) (115530441 / 200000000) (Real.log (890925048613 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (890925048613 / 500000000000) = -Real.log (500000000000 / 890925048613) := by
    rw [show ((890925048613 / 500000000000) : ℝ) = ((500000000000 / 890925048613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (16456997 / 40000000) ≤ -Real.log (500000000000 / 754483209369) ∧
    -Real.log (500000000000 / 754483209369) ≤ (205712463 / 500000000) := by
  have h := checkLog_sound (w := (254483209369 / 1254483209369)) (n := 12)
    (lo := (16456997 / 40000000)) (hi := (205712463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754483209369 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754483209369 / 500000000000) = 1/(500000000000 / 754483209369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (16456997 / 40000000) (205712463 / 500000000) (Real.log (754483209369 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (754483209369 / 500000000000) = -Real.log (500000000000 / 754483209369) := by
    rw [show ((754483209369 / 500000000000) : ℝ) = ((500000000000 / 754483209369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (103023631 / 250000000) ≤ -Real.log (125000000000 / 188747144901) ∧
    -Real.log (125000000000 / 188747144901) ≤ (16483781 / 40000000) := by
  have h := checkLog_sound (w := (63747144901 / 313747144901)) (n := 12)
    (lo := (103023631 / 250000000)) (hi := (16483781 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188747144901 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188747144901 / 125000000000) = 1/(125000000000 / 188747144901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (103023631 / 250000000) (16483781 / 40000000) (Real.log (188747144901 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (188747144901 / 125000000000) = -Real.log (125000000000 / 188747144901) := by
    rw [show ((188747144901 / 125000000000) : ℝ) = ((125000000000 / 188747144901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2107921 / 50000000) ≤ -Real.log (2396794719 / 2500000000) ∧
    -Real.log (2396794719 / 2500000000) ≤ (42158421 / 1000000000) := by
  have h := checkLog_sound (w := (103205281 / 4896794719)) (n := 12)
    (lo := (2107921 / 50000000)) (hi := (42158421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2396794719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2396794719) = 1/(2396794719 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-42158421 / 1000000000) (-2107921 / 50000000) (Real.log (2396794719 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (42022479 / 1000000000) ≤ -Real.log (958848226119 / 1000000000000) ∧
    -Real.log (958848226119 / 1000000000000) ≤ (525281 / 12500000) := by
  have h := checkLog_sound (w := (41151773881 / 1958848226119)) (n := 12)
    (lo := (42022479 / 1000000000)) (hi := (525281 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958848226119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958848226119) = 1/(958848226119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-525281 / 12500000) (-42022479 / 1000000000) (Real.log (958848226119 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell246
