import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell053
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

theorem reflection_log_1_neg : (49628199 / 200000000) ≤ -Real.log (2560 / 3281) ∧
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


theorem reflection_log_1 : Bounds (49628199 / 200000000) (62035249 / 250000000) (Real.log (3281 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3281 / 2560) = -Real.log (2560 / 3281) := by
    rw [show ((3281 / 2560) : ℝ) = ((2560 / 3281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (10337041 / 31250000) ≤ -Real.log (1839 / 2560) ∧
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


theorem reflection_log_2 : Bounds (-330785313 / 1000000000) (-10337041 / 31250000) (Real.log (1839 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (247683713 / 1000000000) ≤ -Real.log (5120 / 6559) ∧
    -Real.log (5120 / 6559) ≤ (123841857 / 500000000) := by
  have h := checkLog_sound (w := (1439 / 11679)) (n := 12)
    (lo := (247683713 / 1000000000)) (hi := (123841857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6559 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6559 / 5120) = 1/(5120 / 6559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (247683713 / 1000000000) (123841857 / 500000000) (Real.log (6559 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6559 / 5120) = -Real.log (5120 / 6559) := by
    rw [show ((6559 / 5120) : ℝ) = ((5120 / 6559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (5155781 / 15625000) ≤ -Real.log (3681 / 5120) ∧
    -Real.log (3681 / 5120) ≤ (65993997 / 200000000) := by
  have h := checkLog_sound (w := (1439 / 8801)) (n := 12)
    (lo := (5155781 / 15625000)) (hi := (65993997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3681) = 1/(3681 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65993997 / 200000000) (-5155781 / 15625000) (Real.log (3681 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45457859 / 250000000) ≤ -Real.log (250000 / 299853) ∧
    -Real.log (250000 / 299853) ≤ (181831437 / 1000000000) := by
  have h := checkLog_sound (w := (49853 / 549853)) (n := 12)
    (lo := (45457859 / 250000000)) (hi := (181831437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299853 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299853 / 250000) = 1/(250000 / 299853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45457859 / 250000000) (181831437 / 1000000000) (Real.log (299853 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (299853 / 250000) = -Real.log (250000 / 299853) := by
    rw [show ((299853 / 250000) : ℝ) = ((250000 / 299853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (222408821 / 1000000000) ≤ -Real.log (200147 / 250000) ∧
    -Real.log (200147 / 250000) ≤ (111204411 / 500000000) := by
  have h := checkLog_sound (w := (49853 / 450147)) (n := 12)
    (lo := (222408821 / 1000000000)) (hi := (111204411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 200147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 200147) = 1/(200147 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-111204411 / 500000000) (-222408821 / 1000000000) (Real.log (200147 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (182180713 / 1000000000) ≤ -Real.log (1000000 / 1199831) ∧
    -Real.log (1000000 / 1199831) ≤ (91090357 / 500000000) := by
  have h := checkLog_sound (w := (199831 / 2199831)) (n := 12)
    (lo := (182180713 / 1000000000)) (hi := (91090357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199831 / 1000000) = 1/(1000000 / 1199831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (182180713 / 1000000000) (91090357 / 500000000) (Real.log (1199831 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1199831 / 1000000) = -Real.log (1000000 / 1199831) := by
    rw [show ((1199831 / 1000000) : ℝ) = ((1000000 / 1199831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (222932323 / 1000000000) ≤ -Real.log (800169 / 1000000) ∧
    -Real.log (800169 / 1000000) ≤ (55733081 / 250000000) := by
  have h := checkLog_sound (w := (199831 / 1800169)) (n := 12)
    (lo := (222932323 / 1000000000)) (hi := (55733081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800169) = 1/(800169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-55733081 / 250000000) (-222932323 / 1000000000) (Real.log (800169 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (66642681 / 500000000) ≤ -Real.log (62500 / 71411) ∧
    -Real.log (62500 / 71411) ≤ (133285363 / 1000000000) := by
  have h := checkLog_sound (w := (8911 / 133911)) (n := 12)
    (lo := (66642681 / 500000000)) (hi := (133285363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71411 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71411 / 62500) = 1/(62500 / 71411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (66642681 / 500000000) (133285363 / 1000000000) (Real.log (71411 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (71411 / 62500) = -Real.log (62500 / 71411) := by
    rw [show ((71411 / 62500) : ℝ) = ((62500 / 71411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (153822733 / 1000000000) ≤ -Real.log (53589 / 62500) ∧
    -Real.log (53589 / 62500) ≤ (76911367 / 500000000) := by
  have h := checkLog_sound (w := (8911 / 116089)) (n := 12)
    (lo := (153822733 / 1000000000)) (hi := (76911367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 53589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 53589) = 1/(53589 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-76911367 / 500000000) (-153822733 / 1000000000) (Real.log (53589 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (133554017 / 1000000000) ≤ -Real.log (1000000 / 1142883) ∧
    -Real.log (1000000 / 1142883) ≤ (66777009 / 500000000) := by
  have h := checkLog_sound (w := (142883 / 2142883)) (n := 12)
    (lo := (133554017 / 1000000000)) (hi := (66777009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142883 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1142883 / 1000000) = 1/(1000000 / 1142883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (133554017 / 1000000000) (66777009 / 500000000) (Real.log (1142883 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1142883 / 1000000) = -Real.log (1000000 / 1142883) := by
    rw [show ((1142883 / 1000000) : ℝ) = ((1000000 / 1142883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (77090423 / 500000000) ≤ -Real.log (857117 / 1000000) ∧
    -Real.log (857117 / 1000000) ≤ (154180847 / 1000000000) := by
  have h := checkLog_sound (w := (142883 / 1857117)) (n := 12)
    (lo := (77090423 / 500000000)) (hi := (154180847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 857117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 857117) = 1/(857117 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-154180847 / 1000000000) (-77090423 / 500000000) (Real.log (857117 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (577653697 / 1000000000) ≤ -Real.log (500000000000 / 890926378701) ∧
    -Real.log (500000000000 / 890926378701) ≤ (288826849 / 500000000) := by
  have h := checkLog_sound (w := (390926378701 / 1390926378701)) (n := 12)
    (lo := (577653697 / 1000000000)) (hi := (288826849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((890926378701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(890926378701 / 500000000000) = 1/(500000000000 / 890926378701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (577653697 / 1000000000) (288826849 / 500000000) (Real.log (890926378701 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (890926378701 / 500000000000) = -Real.log (500000000000 / 890926378701) := by
    rw [show ((890926378701 / 500000000000) : ℝ) = ((500000000000 / 890926378701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (144731577 / 250000000) ≤ -Real.log (100000000000 / 178412180533) ∧
    -Real.log (100000000000 / 178412180533) ≤ (578926309 / 1000000000) := by
  have h := checkLog_sound (w := (78412180533 / 278412180533)) (n := 12)
    (lo := (144731577 / 250000000)) (hi := (578926309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178412180533 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178412180533 / 100000000000) = 1/(100000000000 / 178412180533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (144731577 / 250000000) (578926309 / 1000000000) (Real.log (178412180533 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (178412180533 / 100000000000) = -Real.log (100000000000 / 178412180533) := by
    rw [show ((178412180533 / 100000000000) : ℝ) = ((100000000000 / 178412180533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (404240257 / 1000000000) ≤ -Real.log (100000000000 / 149816384957) ∧
    -Real.log (100000000000 / 149816384957) ≤ (202120129 / 500000000) := by
  have h := checkLog_sound (w := (49816384957 / 249816384957)) (n := 12)
    (lo := (404240257 / 1000000000)) (hi := (202120129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149816384957 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149816384957 / 100000000000) = 1/(100000000000 / 149816384957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (404240257 / 1000000000) (202120129 / 500000000) (Real.log (149816384957 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (149816384957 / 100000000000) = -Real.log (100000000000 / 149816384957) := by
    rw [show ((149816384957 / 100000000000) : ℝ) = ((100000000000 / 149816384957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (405113037 / 1000000000) ≤ -Real.log (62500000000 / 93716999159) ∧
    -Real.log (62500000000 / 93716999159) ≤ (202556519 / 500000000) := by
  have h := checkLog_sound (w := (31216999159 / 156216999159)) (n := 12)
    (lo := (405113037 / 1000000000)) (hi := (202556519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93716999159 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93716999159 / 62500000000) = 1/(62500000000 / 93716999159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (405113037 / 1000000000) (202556519 / 500000000) (Real.log (93716999159 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (93716999159 / 62500000000) = -Real.log (62500000000 / 93716999159) := by
    rw [show ((93716999159 / 62500000000) : ℝ) = ((62500000000 / 93716999159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (57421619 / 200000000) ≤ -Real.log (500000000000 / 666284125473) ∧
    -Real.log (500000000000 / 666284125473) ≤ (560758 / 1953125) := by
  have h := checkLog_sound (w := (166284125473 / 1166284125473)) (n := 12)
    (lo := (57421619 / 200000000)) (hi := (560758 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666284125473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666284125473 / 500000000000) = 1/(500000000000 / 666284125473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (57421619 / 200000000) (560758 / 1953125) (Real.log (666284125473 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (666284125473 / 500000000000) = -Real.log (500000000000 / 666284125473) := by
    rw [show ((666284125473 / 500000000000) : ℝ) = ((500000000000 / 666284125473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (17983429 / 62500000) ≤ -Real.log (500000000000 / 666701862173) ∧
    -Real.log (500000000000 / 666701862173) ≤ (57546973 / 200000000) := by
  have h := checkLog_sound (w := (166701862173 / 1166701862173)) (n := 12)
    (lo := (17983429 / 62500000)) (hi := (57546973 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((666701862173 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(666701862173 / 500000000000) = 1/(500000000000 / 666701862173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (17983429 / 62500000) (57546973 / 200000000) (Real.log (666701862173 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (666701862173 / 500000000000) = -Real.log (500000000000 / 666701862173) := by
    rw [show ((666701862173 / 500000000000) : ℝ) = ((500000000000 / 666701862173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20626829 / 1000000000) ≤ -Real.log (979584448311 / 1000000000000) ∧
    -Real.log (979584448311 / 1000000000000) ≤ (2062683 / 100000000) := by
  have h := checkLog_sound (w := (20415551689 / 1979584448311)) (n := 12)
    (lo := (20626829 / 1000000000)) (hi := (2062683 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979584448311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979584448311) = 1/(979584448311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2062683 / 100000000) (-20626829 / 1000000000) (Real.log (979584448311 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20537371 / 1000000000) ≤ -Real.log (3826844079 / 3906250000) ∧
    -Real.log (3826844079 / 3906250000) ≤ (5134343 / 250000000) := by
  have h := checkLog_sound (w := (79405921 / 7733094079)) (n := 12)
    (lo := (20537371 / 1000000000)) (hi := (5134343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3826844079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3826844079) = 1/(3826844079 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5134343 / 250000000) (-20537371 / 1000000000) (Real.log (3826844079 / 3906250000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell053
