import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell214
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

theorem reflection_log_1_neg : (159581853 / 500000000) ≤ -Real.log (1024 / 1409) ∧
    -Real.log (1024 / 1409) ≤ (319163707 / 1000000000) := by
  have h := checkLog_sound (w := (385 / 2433)) (n := 12)
    (lo := (159581853 / 500000000)) (hi := (319163707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1409 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1409 / 1024) = 1/(1024 / 1409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (159581853 / 500000000) (319163707 / 1000000000) (Real.log (1409 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1409 / 1024) = -Real.log (1024 / 1409) := by
    rw [show ((1409 / 1024) : ℝ) = ((1024 / 1409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (471567351 / 1000000000) ≤ -Real.log (639 / 1024) ∧
    -Real.log (639 / 1024) ≤ (58945919 / 125000000) := by
  have h := checkLog_sound (w := (385 / 1663)) (n := 12)
    (lo := (471567351 / 1000000000)) (hi := (58945919 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 639) = 1/(639 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-58945919 / 125000000) (-471567351 / 1000000000) (Real.log (639 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (318737781 / 1000000000) ≤ -Real.log (2560 / 3521) ∧
    -Real.log (2560 / 3521) ≤ (159368891 / 500000000) := by
  have h := checkLog_sound (w := (961 / 6081)) (n := 12)
    (lo := (318737781 / 1000000000)) (hi := (159368891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3521 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3521 / 2560) = 1/(2560 / 3521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (318737781 / 1000000000) (159368891 / 500000000) (Real.log (3521 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3521 / 2560) = -Real.log (2560 / 3521) := by
    rw [show ((3521 / 2560) : ℝ) = ((2560 / 3521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (58828603 / 125000000) ≤ -Real.log (1599 / 2560) ∧
    -Real.log (1599 / 2560) ≤ (18825153 / 40000000) := by
  have h := checkLog_sound (w := (961 / 4159)) (n := 12)
    (lo := (58828603 / 125000000)) (hi := (18825153 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1599) = 1/(1599 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-18825153 / 40000000) (-58828603 / 125000000) (Real.log (1599 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (118364623 / 500000000) ≤ -Real.log (500000 / 633549) ∧
    -Real.log (500000 / 633549) ≤ (236729247 / 1000000000) := by
  have h := checkLog_sound (w := (133549 / 1133549)) (n := 12)
    (lo := (118364623 / 500000000)) (hi := (236729247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633549 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633549 / 500000) = 1/(500000 / 633549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (118364623 / 500000000) (236729247 / 1000000000) (Real.log (633549 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (633549 / 500000) = -Real.log (500000 / 633549) := by
    rw [show ((633549 / 500000) : ℝ) = ((500000 / 633549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (310743283 / 1000000000) ≤ -Real.log (366451 / 500000) ∧
    -Real.log (366451 / 500000) ≤ (77685821 / 250000000) := by
  have h := checkLog_sound (w := (133549 / 866451)) (n := 12)
    (lo := (310743283 / 1000000000)) (hi := (77685821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 366451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 366451) = 1/(366451 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-77685821 / 250000000) (-310743283 / 1000000000) (Real.log (366451 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (14816439 / 62500000) ≤ -Real.log (1000000 / 1267521) ∧
    -Real.log (1000000 / 1267521) ≤ (9482521 / 40000000) := by
  have h := checkLog_sound (w := (267521 / 2267521)) (n := 12)
    (lo := (14816439 / 62500000)) (hi := (9482521 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267521 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267521 / 1000000) = 1/(1000000 / 1267521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (14816439 / 62500000) (9482521 / 40000000) (Real.log (1267521 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1267521 / 1000000) = -Real.log (1000000 / 1267521) := by
    rw [show ((1267521 / 1000000) : ℝ) = ((1000000 / 1267521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (311320607 / 1000000000) ≤ -Real.log (732479 / 1000000) ∧
    -Real.log (732479 / 1000000) ≤ (9728769 / 31250000) := by
  have h := checkLog_sound (w := (267521 / 1732479)) (n := 12)
    (lo := (311320607 / 1000000000)) (hi := (9728769 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732479) = 1/(732479 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9728769 / 31250000) (-311320607 / 1000000000) (Real.log (732479 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35239569 / 200000000) ≤ -Real.log (500000 / 596337) ∧
    -Real.log (500000 / 596337) ≤ (88098923 / 500000000) := by
  have h := checkLog_sound (w := (96337 / 1096337)) (n := 12)
    (lo := (35239569 / 200000000)) (hi := (88098923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596337 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596337 / 500000) = 1/(500000 / 596337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35239569 / 200000000) (88098923 / 500000000) (Real.log (596337 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (596337 / 500000) = -Real.log (500000 / 596337) := by
    rw [show ((596337 / 500000) : ℝ) = ((500000 / 596337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (107013863 / 500000000) ≤ -Real.log (403663 / 500000) ∧
    -Real.log (403663 / 500000) ≤ (214027727 / 1000000000) := by
  have h := checkLog_sound (w := (96337 / 903663)) (n := 12)
    (lo := (107013863 / 500000000)) (hi := (214027727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403663) = 1/(403663 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-214027727 / 1000000000) (-107013863 / 500000000) (Real.log (403663 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (176464437 / 1000000000) ≤ -Real.log (31250 / 37281) ∧
    -Real.log (31250 / 37281) ≤ (88232219 / 500000000) := by
  have h := checkLog_sound (w := (6031 / 68531)) (n := 12)
    (lo := (176464437 / 1000000000)) (hi := (88232219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37281 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37281 / 31250) = 1/(31250 / 37281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (176464437 / 1000000000) (88232219 / 500000000) (Real.log (37281 / 31250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (37281 / 31250) = -Real.log (31250 / 37281) := by
    rw [show ((37281 / 31250) : ℝ) = ((31250 / 37281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (214421697 / 1000000000) ≤ -Real.log (25219 / 31250) ∧
    -Real.log (25219 / 31250) ≤ (107210849 / 500000000) := by
  have h := checkLog_sound (w := (6031 / 56469)) (n := 12)
    (lo := (214421697 / 1000000000)) (hi := (107210849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 25219) = 1/(25219 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-107210849 / 500000000) (-214421697 / 1000000000) (Real.log (25219 / 31250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (157873321 / 200000000) ≤ -Real.log (50000000000 / 110100062539) ∧
    -Real.log (50000000000 / 110100062539) ≤ (789366607 / 1000000000) := by
  have h := checkLog_sound (w := (10100062539 / 210100062539)) (n := 12)
    (lo := (3848777 / 40000000)) (hi := (48109713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110100062539 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(110100062539 / 100000000000) = 1/(50000000000 / 110100062539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (157873321 / 200000000) (789366607 / 1000000000) (Real.log (110100062539 / 50000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (110100062539 / 50000000000) = -Real.log (50000000000 / 110100062539) := by
    rw [show ((110100062539 / 50000000000) : ℝ) = ((50000000000 / 110100062539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (49420691 / 62500000) ≤ -Real.log (125000000000 / 275625978091) ∧
    -Real.log (125000000000 / 275625978091) ≤ (395365529 / 500000000) := by
  have h := checkLog_sound (w := (25625978091 / 525625978091)) (n := 12)
    (lo := (24395969 / 250000000)) (hi := (97583877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275625978091 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(275625978091 / 250000000000) = 1/(125000000000 / 275625978091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (49420691 / 62500000) (395365529 / 500000000) (Real.log (275625978091 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (275625978091 / 125000000000) = -Real.log (125000000000 / 275625978091) := by
    rw [show ((275625978091 / 125000000000) : ℝ) = ((125000000000 / 275625978091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (547472529 / 1000000000) ≤ -Real.log (50000000000 / 86443890179) ∧
    -Real.log (50000000000 / 86443890179) ≤ (54747253 / 100000000) := by
  have h := checkLog_sound (w := (36443890179 / 136443890179)) (n := 12)
    (lo := (547472529 / 1000000000)) (hi := (54747253 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86443890179 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86443890179 / 50000000000) = 1/(50000000000 / 86443890179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (547472529 / 1000000000) (54747253 / 100000000) (Real.log (86443890179 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (86443890179 / 50000000000) = -Real.log (50000000000 / 86443890179) := by
    rw [show ((86443890179 / 50000000000) : ℝ) = ((50000000000 / 86443890179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (548383631 / 1000000000) ≤ -Real.log (500000000000 / 865226852921) ∧
    -Real.log (500000000000 / 865226852921) ≤ (34273977 / 62500000) := by
  have h := checkLog_sound (w := (365226852921 / 1365226852921)) (n := 12)
    (lo := (548383631 / 1000000000)) (hi := (34273977 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((865226852921 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(865226852921 / 500000000000) = 1/(500000000000 / 865226852921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (548383631 / 1000000000) (34273977 / 62500000) (Real.log (865226852921 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (865226852921 / 500000000000) = -Real.log (500000000000 / 865226852921) := by
    rw [show ((865226852921 / 500000000000) : ℝ) = ((500000000000 / 865226852921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (97556393 / 250000000) ≤ -Real.log (100000000000 / 147731399707) ∧
    -Real.log (100000000000 / 147731399707) ≤ (390225573 / 1000000000) := by
  have h := checkLog_sound (w := (47731399707 / 247731399707)) (n := 12)
    (lo := (97556393 / 250000000)) (hi := (390225573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147731399707 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147731399707 / 100000000000) = 1/(100000000000 / 147731399707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (97556393 / 250000000) (390225573 / 1000000000) (Real.log (147731399707 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (147731399707 / 100000000000) = -Real.log (100000000000 / 147731399707) := by
    rw [show ((147731399707 / 100000000000) : ℝ) = ((100000000000 / 147731399707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (195443067 / 500000000) ≤ -Real.log (500000000000 / 739145089021) ∧
    -Real.log (500000000000 / 739145089021) ≤ (78177227 / 200000000) := by
  have h := checkLog_sound (w := (239145089021 / 1239145089021)) (n := 12)
    (lo := (195443067 / 500000000)) (hi := (78177227 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739145089021 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739145089021 / 500000000000) = 1/(500000000000 / 739145089021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (195443067 / 500000000) (78177227 / 200000000) (Real.log (739145089021 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (739145089021 / 500000000000) = -Real.log (500000000000 / 739145089021) := by
    rw [show ((739145089021 / 500000000000) : ℝ) = ((500000000000 / 739145089021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1897863 / 50000000) ≤ -Real.log (940189539 / 976562500) ∧
    -Real.log (940189539 / 976562500) ≤ (37957261 / 1000000000) := by
  have h := checkLog_sound (w := (36372961 / 1916752039)) (n := 12)
    (lo := (1897863 / 50000000)) (hi := (37957261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 940189539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 940189539) = 1/(940189539 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-37957261 / 1000000000) (-1897863 / 50000000) (Real.log (940189539 / 976562500)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (37829881 / 1000000000) ≤ -Real.log (240719182431 / 250000000000) ∧
    -Real.log (240719182431 / 250000000000) ≤ (18914941 / 500000000) := by
  have h := checkLog_sound (w := (9280817569 / 490719182431)) (n := 12)
    (lo := (37829881 / 1000000000)) (hi := (18914941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240719182431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240719182431) = 1/(240719182431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-18914941 / 500000000) (-37829881 / 1000000000) (Real.log (240719182431 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell214
