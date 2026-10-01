import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell054
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

theorem reflection_log_1_neg : (62149517 / 250000000) ≤ -Real.log (1024 / 1313) ∧
    -Real.log (1024 / 1313) ≤ (248598069 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 2337)) (n := 12)
    (lo := (62149517 / 250000000)) (hi := (248598069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1313 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1313 / 1024) = 1/(1024 / 1313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (62149517 / 250000000) (248598069 / 1000000000) (Real.log (1313 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1313 / 1024) = -Real.log (1024 / 1313) := by
    rw [show ((1313 / 1024) : ℝ) = ((1024 / 1313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (165800653 / 500000000) ≤ -Real.log (735 / 1024) ∧
    -Real.log (735 / 1024) ≤ (331601307 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 1759)) (n := 12)
    (lo := (165800653 / 500000000)) (hi := (331601307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 735) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 735) = 1/(735 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-331601307 / 1000000000) (-165800653 / 500000000) (Real.log (735 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (49628199 / 200000000) ≤ -Real.log (2560 / 3281) ∧
    -Real.log (2560 / 3281) ≤ (62035249 / 250000000) := by
  have h := checkLog_sound (w := (721 / 5841)) (n := 12)
    (lo := (49628199 / 200000000)) (hi := (62035249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3281 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3281 / 2560) = 1/(2560 / 3281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (49628199 / 200000000) (62035249 / 250000000) (Real.log (3281 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3281 / 2560) = -Real.log (2560 / 3281) := by
    rw [show ((3281 / 2560) : ℝ) = ((2560 / 3281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (10337041 / 31250000) ≤ -Real.log (1839 / 2560) ∧
    -Real.log (1839 / 2560) ≤ (330785313 / 1000000000) := by
  have h := checkLog_sound (w := (721 / 4399)) (n := 12)
    (lo := (10337041 / 31250000)) (hi := (330785313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1839) = 1/(1839 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-330785313 / 1000000000) (-10337041 / 31250000) (Real.log (1839 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (4554497 / 25000000) ≤ -Real.log (100000 / 119983) ∧
    -Real.log (100000 / 119983) ≤ (182179881 / 1000000000) := by
  have h := checkLog_sound (w := (19983 / 219983)) (n := 12)
    (lo := (4554497 / 25000000)) (hi := (182179881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119983 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119983 / 100000) = 1/(100000 / 119983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (4554497 / 25000000) (182179881 / 1000000000) (Real.log (119983 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (119983 / 100000) = -Real.log (100000 / 119983) := by
    rw [show ((119983 / 100000) : ℝ) = ((100000 / 119983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (222931073 / 1000000000) ≤ -Real.log (80017 / 100000) ∧
    -Real.log (80017 / 100000) ≤ (111465537 / 500000000) := by
  have h := checkLog_sound (w := (19983 / 180017)) (n := 12)
    (lo := (222931073 / 1000000000)) (hi := (111465537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 80017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 80017) = 1/(80017 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-111465537 / 500000000) (-222931073 / 1000000000) (Real.log (80017 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (45632467 / 250000000) ≤ -Real.log (4000 / 4801) ∧
    -Real.log (4000 / 4801) ≤ (182529869 / 1000000000) := by
  have h := checkLog_sound (w := (801 / 8801)) (n := 12)
    (lo := (45632467 / 250000000)) (hi := (182529869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4801 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4801 / 4000) = 1/(4000 / 4801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (45632467 / 250000000) (182529869 / 1000000000) (Real.log (4801 / 4000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4801 / 4000) = -Real.log (4000 / 4801) := by
    rw [show ((4801 / 4000) : ℝ) = ((4000 / 4801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2234561 / 10000000) ≤ -Real.log (3199 / 4000) ∧
    -Real.log (3199 / 4000) ≤ (223456101 / 1000000000) := by
  have h := checkLog_sound (w := (801 / 7199)) (n := 12)
    (lo := (2234561 / 10000000)) (hi := (223456101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 3199) = 1/(3199 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-223456101 / 1000000000) (-2234561 / 10000000) (Real.log (3199 / 4000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (66776571 / 500000000) ≤ -Real.log (500000 / 571441) ∧
    -Real.log (500000 / 571441) ≤ (133553143 / 1000000000) := by
  have h := checkLog_sound (w := (71441 / 1071441)) (n := 12)
    (lo := (66776571 / 500000000)) (hi := (133553143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((571441 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(571441 / 500000) = 1/(500000 / 571441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (66776571 / 500000000) (133553143 / 1000000000) (Real.log (571441 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (571441 / 500000) = -Real.log (500000 / 571441) := by
    rw [show ((571441 / 500000) : ℝ) = ((500000 / 571441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (963623 / 6250000) ≤ -Real.log (428559 / 500000) ∧
    -Real.log (428559 / 500000) ≤ (154179681 / 1000000000) := by
  have h := checkLog_sound (w := (71441 / 928559)) (n := 12)
    (lo := (963623 / 6250000)) (hi := (154179681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 428559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 428559) = 1/(428559 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-154179681 / 1000000000) (-963623 / 6250000) (Real.log (428559 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (669113 / 5000000) ≤ -Real.log (100000 / 114319) ∧
    -Real.log (100000 / 114319) ≤ (133822601 / 1000000000) := by
  have h := checkLog_sound (w := (14319 / 214319)) (n := 12)
    (lo := (669113 / 5000000)) (hi := (133822601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114319 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114319 / 100000) = 1/(100000 / 114319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (669113 / 5000000) (133822601 / 1000000000) (Real.log (114319 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (114319 / 100000) = -Real.log (100000 / 114319) := by
    rw [show ((114319 / 100000) : ℝ) = ((100000 / 114319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (9658693 / 62500000) ≤ -Real.log (85681 / 100000) ∧
    -Real.log (85681 / 100000) ≤ (154539089 / 1000000000) := by
  have h := checkLog_sound (w := (14319 / 185681)) (n := 12)
    (lo := (9658693 / 62500000)) (hi := (154539089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 85681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 85681) = 1/(85681 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-154539089 / 1000000000) (-9658693 / 62500000) (Real.log (85681 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (144731577 / 250000000) ≤ -Real.log (62500000000 / 111507612833) ∧
    -Real.log (62500000000 / 111507612833) ≤ (578926309 / 1000000000) := by
  have h := checkLog_sound (w := (49007612833 / 174007612833)) (n := 12)
    (lo := (144731577 / 250000000)) (hi := (578926309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111507612833 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111507612833 / 62500000000) = 1/(62500000000 / 111507612833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (144731577 / 250000000) (578926309 / 1000000000) (Real.log (111507612833 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (111507612833 / 62500000000) = -Real.log (62500000000 / 111507612833) := by
    rw [show ((111507612833 / 62500000000) : ℝ) = ((62500000000 / 111507612833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (928319 / 1600000) ≤ -Real.log (7812500000 / 13956207483) ∧
    -Real.log (7812500000 / 13956207483) ≤ (36262461 / 62500000) := by
  have h := checkLog_sound (w := (6143707483 / 21768707483)) (n := 12)
    (lo := (928319 / 1600000)) (hi := (36262461 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13956207483 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13956207483 / 7812500000) = 1/(7812500000 / 13956207483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (928319 / 1600000) (36262461 / 62500000) (Real.log (13956207483 / 7812500000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (13956207483 / 7812500000) = -Real.log (7812500000 / 13956207483) := by
    rw [show ((13956207483 / 7812500000) : ℝ) = ((7812500000 / 13956207483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (405110953 / 1000000000) ≤ -Real.log (500000000000 / 749734431433) ∧
    -Real.log (500000000000 / 749734431433) ≤ (202555477 / 500000000) := by
  have h := checkLog_sound (w := (249734431433 / 1249734431433)) (n := 12)
    (lo := (405110953 / 1000000000)) (hi := (202555477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749734431433 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749734431433 / 500000000000) = 1/(500000000000 / 749734431433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (405110953 / 1000000000) (202555477 / 500000000) (Real.log (749734431433 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (749734431433 / 500000000000) = -Real.log (500000000000 / 749734431433) := by
    rw [show ((749734431433 / 500000000000) : ℝ) = ((500000000000 / 749734431433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (25374123 / 62500000) ≤ -Real.log (500000000000 / 750390747109) ∧
    -Real.log (500000000000 / 750390747109) ≤ (405985969 / 1000000000) := by
  have h := checkLog_sound (w := (250390747109 / 1250390747109)) (n := 12)
    (lo := (25374123 / 62500000)) (hi := (405985969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750390747109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750390747109 / 500000000000) = 1/(500000000000 / 750390747109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (25374123 / 62500000) (405985969 / 1000000000) (Real.log (750390747109 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (750390747109 / 500000000000) = -Real.log (500000000000 / 750390747109) := by
    rw [show ((750390747109 / 500000000000) : ℝ) = ((500000000000 / 750390747109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (143866411 / 500000000) ≤ -Real.log (500000000000 / 666700500981) ∧
    -Real.log (500000000000 / 666700500981) ≤ (287732823 / 1000000000) := by
  have h := checkLog_sound (w := (166700500981 / 1166700500981)) (n := 12)
    (lo := (143866411 / 500000000)) (hi := (287732823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666700500981 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666700500981 / 500000000000) = 1/(500000000000 / 666700500981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (143866411 / 500000000) (287732823 / 1000000000) (Real.log (666700500981 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (666700500981 / 500000000000) = -Real.log (500000000000 / 666700500981) := by
    rw [show ((666700500981 / 500000000000) : ℝ) = ((500000000000 / 666700500981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (36045211 / 125000000) ≤ -Real.log (125000000000 / 166779974557) ∧
    -Real.log (125000000000 / 166779974557) ≤ (288361689 / 1000000000) := by
  have h := checkLog_sound (w := (41779974557 / 291779974557)) (n := 12)
    (lo := (36045211 / 125000000)) (hi := (288361689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166779974557 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166779974557 / 125000000000) = 1/(125000000000 / 166779974557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (36045211 / 125000000) (288361689 / 1000000000) (Real.log (166779974557 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (166779974557 / 125000000000) = -Real.log (125000000000 / 166779974557) := by
    rw [show ((166779974557 / 125000000000) : ℝ) = ((125000000000 / 166779974557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2589561 / 125000000) ≤ -Real.log (9794966239 / 10000000000) ∧
    -Real.log (9794966239 / 10000000000) ≤ (20716489 / 1000000000) := by
  have h := checkLog_sound (w := (205033761 / 19794966239)) (n := 12)
    (lo := (2589561 / 125000000)) (hi := (20716489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9794966239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9794966239) = 1/(9794966239 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-20716489 / 1000000000) (-2589561 / 125000000) (Real.log (9794966239 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20626537 / 1000000000) ≤ -Real.log (244896183519 / 250000000000) ∧
    -Real.log (244896183519 / 250000000000) ≤ (10313269 / 500000000) := by
  have h := checkLog_sound (w := (5103816481 / 494896183519)) (n := 12)
    (lo := (20626537 / 1000000000)) (hi := (10313269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244896183519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244896183519) = 1/(244896183519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10313269 / 500000000) (-20626537 / 1000000000) (Real.log (244896183519 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell054
