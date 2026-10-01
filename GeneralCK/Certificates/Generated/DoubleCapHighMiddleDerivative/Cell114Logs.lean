import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell114
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

theorem reflection_log_1_neg : (5512941 / 20000000) ≤ -Real.log (1024 / 1349) ∧
    -Real.log (1024 / 1349) ≤ (275647051 / 1000000000) := by
  have h := checkLog_sound (w := (325 / 2373)) (n := 12)
    (lo := (5512941 / 20000000)) (hi := (275647051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1349 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1349 / 1024) = 1/(1024 / 1349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5512941 / 20000000) (275647051 / 1000000000) (Real.log (1349 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1349 / 1024) = -Real.log (1024 / 1349) := by
    rw [show ((1349 / 1024) : ℝ) = ((1024 / 1349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (381821063 / 1000000000) ≤ -Real.log (699 / 1024) ∧
    -Real.log (699 / 1024) ≤ (47727633 / 125000000) := by
  have h := checkLog_sound (w := (325 / 1723)) (n := 12)
    (lo := (381821063 / 1000000000)) (hi := (47727633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 699) = 1/(699 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-47727633 / 125000000) (-381821063 / 1000000000) (Real.log (699 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (275202177 / 1000000000) ≤ -Real.log (2560 / 3371) ∧
    -Real.log (2560 / 3371) ≤ (137601089 / 500000000) := by
  have h := checkLog_sound (w := (811 / 5931)) (n := 12)
    (lo := (275202177 / 1000000000)) (hi := (137601089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3371 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3371 / 2560) = 1/(2560 / 3371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (275202177 / 1000000000) (137601089 / 500000000) (Real.log (3371 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3371 / 2560) = -Real.log (2560 / 3371) := by
    rw [show ((3371 / 2560) : ℝ) = ((2560 / 3371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (190481531 / 500000000) ≤ -Real.log (1749 / 2560) ∧
    -Real.log (1749 / 2560) ≤ (380963063 / 1000000000) := by
  have h := checkLog_sound (w := (811 / 4309)) (n := 12)
    (lo := (190481531 / 500000000)) (hi := (380963063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1749) = 1/(1749 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-380963063 / 1000000000) (-190481531 / 500000000) (Real.log (1749 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (202930231 / 1000000000) ≤ -Real.log (1000000 / 1224987) ∧
    -Real.log (1000000 / 1224987) ≤ (25366279 / 125000000) := by
  have h := checkLog_sound (w := (224987 / 2224987)) (n := 12)
    (lo := (202930231 / 1000000000)) (hi := (25366279 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1224987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1224987 / 1000000) = 1/(1000000 / 1224987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (202930231 / 1000000000) (25366279 / 125000000) (Real.log (1224987 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1224987 / 1000000) = -Real.log (1000000 / 1224987) := by
    rw [show ((1224987 / 1000000) : ℝ) = ((1000000 / 1224987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (10195019 / 40000000) ≤ -Real.log (775013 / 1000000) ∧
    -Real.log (775013 / 1000000) ≤ (63718869 / 250000000) := by
  have h := checkLog_sound (w := (224987 / 1775013)) (n := 12)
    (lo := (10195019 / 40000000)) (hi := (63718869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 775013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 775013) = 1/(775013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-63718869 / 250000000) (-10195019 / 40000000) (Real.log (775013 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (203273033 / 1000000000) ≤ -Real.log (1000000 / 1225407) ∧
    -Real.log (1000000 / 1225407) ≤ (101636517 / 500000000) := by
  have h := checkLog_sound (w := (225407 / 2225407)) (n := 12)
    (lo := (203273033 / 1000000000)) (hi := (101636517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1225407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1225407 / 1000000) = 1/(1000000 / 1225407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (203273033 / 1000000000) (101636517 / 500000000) (Real.log (1225407 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1225407 / 1000000) = -Real.log (1000000 / 1225407) := by
    rw [show ((1225407 / 1000000) : ℝ) = ((1000000 / 1225407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (63854387 / 250000000) ≤ -Real.log (774593 / 1000000) ∧
    -Real.log (774593 / 1000000) ≤ (255417549 / 1000000000) := by
  have h := checkLog_sound (w := (225407 / 1774593)) (n := 12)
    (lo := (63854387 / 250000000)) (hi := (255417549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 774593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 774593) = 1/(774593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-255417549 / 1000000000) (-63854387 / 250000000) (Real.log (774593 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18698213 / 125000000) ≤ -Real.log (1000000 / 1161353) ∧
    -Real.log (1000000 / 1161353) ≤ (29917141 / 200000000) := by
  have h := checkLog_sound (w := (161353 / 2161353)) (n := 12)
    (lo := (18698213 / 125000000)) (hi := (29917141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161353 / 1000000) = 1/(1000000 / 1161353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18698213 / 125000000) (29917141 / 200000000) (Real.log (1161353 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1161353 / 1000000) = -Real.log (1000000 / 1161353) := by
    rw [show ((1161353 / 1000000) : ℝ) = ((1000000 / 1161353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (879827 / 5000000) ≤ -Real.log (838647 / 1000000) ∧
    -Real.log (838647 / 1000000) ≤ (175965401 / 1000000000) := by
  have h := checkLog_sound (w := (161353 / 1838647)) (n := 12)
    (lo := (879827 / 5000000)) (hi := (175965401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 838647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 838647) = 1/(838647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-175965401 / 1000000000) (-879827 / 5000000) (Real.log (838647 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (149852599 / 1000000000) ≤ -Real.log (1000000 / 1161663) ∧
    -Real.log (1000000 / 1161663) ≤ (749263 / 5000000) := by
  have h := checkLog_sound (w := (161663 / 2161663)) (n := 12)
    (lo := (149852599 / 1000000000)) (hi := (749263 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161663 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161663 / 1000000) = 1/(1000000 / 1161663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (149852599 / 1000000000) (749263 / 5000000) (Real.log (1161663 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1161663 / 1000000) = -Real.log (1000000 / 1161663) := by
    rw [show ((1161663 / 1000000) : ℝ) = ((1000000 / 1161663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (176335111 / 1000000000) ≤ -Real.log (838337 / 1000000) ∧
    -Real.log (838337 / 1000000) ≤ (22041889 / 125000000) := by
  have h := checkLog_sound (w := (161663 / 1838337)) (n := 12)
    (lo := (176335111 / 1000000000)) (hi := (22041889 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 838337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 838337) = 1/(838337 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-22041889 / 125000000) (-176335111 / 1000000000) (Real.log (838337 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (16404131 / 25000000) ≤ -Real.log (100000000000 / 192738707833) ∧
    -Real.log (100000000000 / 192738707833) ≤ (656165241 / 1000000000) := by
  have h := checkLog_sound (w := (92738707833 / 292738707833)) (n := 12)
    (lo := (16404131 / 25000000)) (hi := (656165241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192738707833 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192738707833 / 100000000000) = 1/(100000000000 / 192738707833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (16404131 / 25000000) (656165241 / 1000000000) (Real.log (192738707833 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (192738707833 / 100000000000) = -Real.log (100000000000 / 192738707833) := by
    rw [show ((192738707833 / 100000000000) : ℝ) = ((100000000000 / 192738707833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (657468113 / 1000000000) ≤ -Real.log (50000000000 / 96494992847) ∧
    -Real.log (50000000000 / 96494992847) ≤ (328734057 / 500000000) := by
  have h := checkLog_sound (w := (46494992847 / 146494992847)) (n := 12)
    (lo := (657468113 / 1000000000)) (hi := (328734057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96494992847 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96494992847 / 50000000000) = 1/(50000000000 / 96494992847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (657468113 / 1000000000) (328734057 / 500000000) (Real.log (96494992847 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (96494992847 / 50000000000) = -Real.log (50000000000 / 96494992847) := by
    rw [show ((96494992847 / 50000000000) : ℝ) = ((50000000000 / 96494992847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (457805707 / 1000000000) ≤ -Real.log (500000000000 / 790300936887) ∧
    -Real.log (500000000000 / 790300936887) ≤ (114451427 / 250000000) := by
  have h := checkLog_sound (w := (290300936887 / 1290300936887)) (n := 12)
    (lo := (457805707 / 1000000000)) (hi := (114451427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((790300936887 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(790300936887 / 500000000000) = 1/(500000000000 / 790300936887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (457805707 / 1000000000) (114451427 / 250000000) (Real.log (790300936887 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (790300936887 / 500000000000) = -Real.log (500000000000 / 790300936887) := by
    rw [show ((790300936887 / 500000000000) : ℝ) = ((500000000000 / 790300936887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (229345291 / 500000000) ≤ -Real.log (62500000000 / 98875070521) ∧
    -Real.log (62500000000 / 98875070521) ≤ (458690583 / 1000000000) := by
  have h := checkLog_sound (w := (36375070521 / 161375070521)) (n := 12)
    (lo := (229345291 / 500000000)) (hi := (458690583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98875070521 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98875070521 / 62500000000) = 1/(62500000000 / 98875070521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (229345291 / 500000000) (458690583 / 1000000000) (Real.log (98875070521 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (98875070521 / 62500000000) = -Real.log (62500000000 / 98875070521) := by
    rw [show ((98875070521 / 62500000000) : ℝ) = ((62500000000 / 98875070521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (635842 / 1953125) ≤ -Real.log (500000000000 / 692396801037) ∧
    -Real.log (500000000000 / 692396801037) ≤ (65110221 / 200000000) := by
  have h := checkLog_sound (w := (192396801037 / 1192396801037)) (n := 12)
    (lo := (635842 / 1953125)) (hi := (65110221 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692396801037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692396801037 / 500000000000) = 1/(500000000000 / 692396801037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (635842 / 1953125) (65110221 / 200000000) (Real.log (692396801037 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (692396801037 / 500000000000) = -Real.log (500000000000 / 692396801037) := by
    rw [show ((692396801037 / 500000000000) : ℝ) = ((500000000000 / 692396801037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (32618771 / 100000000) ≤ -Real.log (125000000000 / 173209431291) ∧
    -Real.log (125000000000 / 173209431291) ≤ (326187711 / 1000000000) := by
  have h := checkLog_sound (w := (48209431291 / 298209431291)) (n := 12)
    (lo := (32618771 / 100000000)) (hi := (326187711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173209431291 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173209431291 / 125000000000) = 1/(125000000000 / 173209431291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (32618771 / 100000000) (326187711 / 1000000000) (Real.log (173209431291 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (173209431291 / 125000000000) = -Real.log (125000000000 / 173209431291) := by
    rw [show ((173209431291 / 125000000000) : ℝ) = ((125000000000 / 173209431291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1655157 / 62500000) ≤ -Real.log (973865074431 / 1000000000000) ∧
    -Real.log (973865074431 / 1000000000000) ≤ (26482513 / 1000000000) := by
  have h := checkLog_sound (w := (26134925569 / 1973865074431)) (n := 12)
    (lo := (1655157 / 62500000)) (hi := (26482513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973865074431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973865074431) = 1/(973865074431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-26482513 / 1000000000) (-1655157 / 62500000) (Real.log (973865074431 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5275939 / 200000000) ≤ -Real.log (973965209391 / 1000000000000) ∧
    -Real.log (973965209391 / 1000000000000) ≤ (1648731 / 62500000) := by
  have h := checkLog_sound (w := (26034790609 / 1973965209391)) (n := 12)
    (lo := (5275939 / 200000000)) (hi := (1648731 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973965209391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973965209391) = 1/(973965209391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1648731 / 62500000) (-5275939 / 200000000) (Real.log (973965209391 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell114
