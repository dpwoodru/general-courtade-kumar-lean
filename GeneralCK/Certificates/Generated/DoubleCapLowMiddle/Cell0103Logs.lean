import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0103
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

theorem reflection_log_1_neg : (33541983 / 50000000) ≤ -Real.log (51200 / 100141) ∧
    -Real.log (51200 / 100141) ≤ (670839661 / 1000000000) := by
  have h := checkLog_sound (w := (48941 / 151341)) (n := 12)
    (lo := (33541983 / 50000000)) (hi := (670839661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100141 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100141 / 51200) = 1/(51200 / 100141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (33541983 / 50000000) (670839661 / 1000000000) (Real.log (100141 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100141 / 51200) = -Real.log (51200 / 100141) := by
    rw [show ((100141 / 51200) : ℝ) = ((51200 / 100141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (780204323 / 250000000) ≤ -Real.log (2259 / 51200) ∧
    -Real.log (2259 / 51200) ≤ (3120817297 / 1000000000) := by
  have h := checkLog_sound (w := (941 / 5459)) (n := 12)
    (lo := (87057143 / 250000000)) (hi := (348228573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2259) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2259) = 1/(2259 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3120817297 / 1000000000) (-780204323 / 250000000) (Real.log (2259 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67064991 / 100000000) ≤ -Real.log (25600 / 50061) ∧
    -Real.log (25600 / 50061) ≤ (670649911 / 1000000000) := by
  have h := checkLog_sound (w := (24461 / 75661)) (n := 12)
    (lo := (67064991 / 100000000)) (hi := (670649911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50061 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50061 / 25600) = 1/(25600 / 50061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67064991 / 100000000) (670649911 / 1000000000) (Real.log (50061 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50061 / 25600) = -Real.log (25600 / 50061) := by
    rw [show ((50061 / 25600) : ℝ) = ((25600 / 50061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (48631901 / 15625000) ≤ -Real.log (1139 / 25600) ∧
    -Real.log (1139 / 25600) ≤ (3112441669 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 2739)) (n := 12)
    (lo := (21240809 / 62500000)) (hi := (67970589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1139) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1139) = 1/(1139 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3112441669 / 1000000000) (-48631901 / 15625000) (Real.log (1139 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (648023139 / 1000000000) ≤ -Real.log (25600 / 48941) ∧
    -Real.log (25600 / 48941) ≤ (32401157 / 50000000) := by
  have h := checkLog_sound (w := (23341 / 74541)) (n := 12)
    (lo := (648023139 / 1000000000)) (hi := (32401157 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48941 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48941 / 25600) = 1/(25600 / 48941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (648023139 / 1000000000) (32401157 / 50000000) (Real.log (48941 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (48941 / 25600) = -Real.log (25600 / 48941) := by
    rw [show ((48941 / 25600) : ℝ) = ((25600 / 48941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (75864691 / 31250000) ≤ -Real.log (2259 / 25600) ∧
    -Real.log (2259 / 25600) ≤ (606917529 / 250000000) := by
  have h := checkLog_sound (w := (941 / 5459)) (n := 12)
    (lo := (87057143 / 250000000)) (hi := (348228573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2259) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2259) = 1/(2259 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-606917529 / 250000000) (-75864691 / 31250000) (Real.log (2259 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (647634841 / 1000000000) ≤ -Real.log (12800 / 24461) ∧
    -Real.log (12800 / 24461) ≤ (323817421 / 500000000) := by
  have h := checkLog_sound (w := (11661 / 37261)) (n := 12)
    (lo := (647634841 / 1000000000)) (hi := (323817421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24461 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24461 / 12800) = 1/(12800 / 24461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (647634841 / 1000000000) (323817421 / 500000000) (Real.log (24461 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24461 / 12800) = -Real.log (12800 / 24461) := by
    rw [show ((24461 / 12800) : ℝ) = ((12800 / 24461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (604823621 / 250000000) ≤ -Real.log (1139 / 12800) ∧
    -Real.log (1139 / 12800) ≤ (302411811 / 125000000) := by
  have h := checkLog_sound (w := (461 / 2739)) (n := 12)
    (lo := (21240809 / 62500000)) (hi := (67970589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1139) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1139) = 1/(1139 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-302411811 / 125000000) (-604823621 / 250000000) (Real.log (1139 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (168692589 / 250000000) ≤ -Real.log (500000 / 981791) ∧
    -Real.log (500000 / 981791) ≤ (674770357 / 1000000000) := by
  have h := checkLog_sound (w := (481791 / 1481791)) (n := 12)
    (lo := (168692589 / 250000000)) (hi := (674770357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981791 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981791 / 500000) = 1/(500000 / 981791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (168692589 / 250000000) (674770357 / 1000000000) (Real.log (981791 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (981791 / 500000) = -Real.log (500000 / 981791) := by
    rw [show ((981791 / 500000) : ℝ) = ((500000 / 981791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1656346059 / 500000000) ≤ -Real.log (18209 / 500000) ∧
    -Real.log (18209 / 500000) ≤ (3312692123 / 1000000000) := by
  have h := checkLog_sound (w := (13041 / 49459)) (n := 12)
    (lo := (270051699 / 500000000)) (hi := (540103399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18209) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18209) = 1/(18209 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3312692123 / 1000000000) (-1656346059 / 500000000) (Real.log (18209 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (674916507 / 1000000000) ≤ -Real.log (1000000 / 1963869) ∧
    -Real.log (1000000 / 1963869) ≤ (168729127 / 250000000) := by
  have h := checkLog_sound (w := (963869 / 2963869)) (n := 12)
    (lo := (674916507 / 1000000000)) (hi := (168729127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963869 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963869 / 1000000) = 1/(1000000 / 1963869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (674916507 / 1000000000) (168729127 / 250000000) (Real.log (1963869 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1963869 / 1000000) = -Real.log (1000000 / 1963869) := by
    rw [show ((1963869 / 1000000) : ℝ) = ((1000000 / 1963869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1660302027 / 500000000) ≤ -Real.log (36131 / 1000000) ∧
    -Real.log (36131 / 1000000) ≤ (3320604059 / 1000000000) := by
  have h := checkLog_sound (w := (26369 / 98631)) (n := 12)
    (lo := (274007667 / 500000000)) (hi := (109603067 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36131) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 36131) = 1/(36131 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3320604059 / 1000000000) (-1660302027 / 500000000) (Real.log (36131 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (337291463 / 500000000) ≤ -Real.log (500000 / 981607) ∧
    -Real.log (500000 / 981607) ≤ (674582927 / 1000000000) := by
  have h := checkLog_sound (w := (481607 / 1481607)) (n := 12)
    (lo := (337291463 / 500000000)) (hi := (674582927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981607 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981607 / 500000) = 1/(500000 / 981607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (337291463 / 500000000) (674582927 / 1000000000) (Real.log (981607 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (981607 / 500000) = -Real.log (500000 / 981607) := by
    rw [show ((981607 / 500000) : ℝ) = ((500000 / 981607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1651318969 / 500000000) ≤ -Real.log (18393 / 500000) ∧
    -Real.log (18393 / 500000) ≤ (3302637943 / 1000000000) := by
  have h := checkLog_sound (w := (12857 / 49643)) (n := 12)
    (lo := (265024609 / 500000000)) (hi := (530049219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18393) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18393) = 1/(18393 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3302637943 / 1000000000) (-1651318969 / 500000000) (Real.log (18393 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (1054269 / 1562500) ≤ -Real.log (1000000 / 1963507) ∧
    -Real.log (1000000 / 1963507) ≤ (674732161 / 1000000000) := by
  have h := checkLog_sound (w := (963507 / 2963507)) (n := 12)
    (lo := (1054269 / 1562500)) (hi := (674732161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963507 / 1000000) = 1/(1000000 / 1963507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (1054269 / 1562500) (674732161 / 1000000000) (Real.log (1963507 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1963507 / 1000000) = -Real.log (1000000 / 1963507) := by
    rw [show ((1963507 / 1000000) : ℝ) = ((1000000 / 1963507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (662126963 / 200000000) ≤ -Real.log (36493 / 1000000) ∧
    -Real.log (36493 / 1000000) ≤ (165531741 / 50000000) := by
  have h := checkLog_sound (w := (26007 / 98993)) (n := 12)
    (lo := (107609219 / 200000000)) (hi := (33627881 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36493) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 36493) = 1/(36493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-165531741 / 50000000) (-662126963 / 200000000) (Real.log (36493 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1993731237 / 500000000) ≤ -Real.log (500000000000 / 26958948871437) ∧
    -Real.log (500000000000 / 26958948871437) ≤ (49843281 / 12500000) := by
  have h := checkLog_sound (w := (10958948871437 / 42958948871437)) (n := 12)
    (lo := (260863287 / 500000000)) (hi := (20869063 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26958948871437 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26958948871437 / 16000000000000) = 1/(500000000000 / 26958948871437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1993731237 / 500000000) (49843281 / 12500000) (Real.log (26958948871437 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (26958948871437 / 500000000000) = -Real.log (500000000000 / 26958948871437) := by
    rw [show ((26958948871437 / 500000000000) : ℝ) = ((500000000000 / 26958948871437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (49944007 / 12500000) ≤ -Real.log (10000000000 / 543541280341) ∧
    -Real.log (10000000000 / 543541280341) ≤ (1997760283 / 500000000) := by
  have h := checkLog_sound (w := (223541280341 / 863541280341)) (n := 12)
    (lo := (26489233 / 50000000)) (hi := (529784661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543541280341 / 320000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(543541280341 / 320000000000) = 1/(10000000000 / 543541280341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (49944007 / 12500000) (1997760283 / 500000000) (Real.log (543541280341 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (543541280341 / 10000000000) = -Real.log (10000000000 / 543541280341) := by
    rw [show ((543541280341 / 10000000000) : ℝ) = ((10000000000 / 543541280341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15536019 / 3906250) ≤ -Real.log (500000000000 / 26684254879573) ∧
    -Real.log (500000000000 / 26684254879573) ≤ (397722087 / 100000000) := by
  have h := checkLog_sound (w := (10684254879573 / 42684254879573)) (n := 12)
    (lo := (127871241 / 250000000)) (hi := (102296993 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26684254879573 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(26684254879573 / 16000000000000) = 1/(500000000000 / 26684254879573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (15536019 / 3906250) (397722087 / 100000000) (Real.log (26684254879573 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (26684254879573 / 500000000000) = -Real.log (500000000000 / 26684254879573) := by
    rw [show ((26684254879573 / 500000000000) : ℝ) = ((500000000000 / 26684254879573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1992683487 / 500000000) ≤ -Real.log (31250000000 / 1681407221933) ∧
    -Real.log (31250000000 / 1681407221933) ≤ (199268349 / 50000000) := by
  have h := checkLog_sound (w := (681407221933 / 2681407221933)) (n := 12)
    (lo := (259815537 / 500000000)) (hi := (20785243 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1681407221933 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1681407221933 / 1000000000000) = 1/(31250000000 / 1681407221933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1992683487 / 500000000) (199268349 / 50000000) (Real.log (1681407221933 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1681407221933 / 31250000000) = -Real.log (31250000000 / 1681407221933) := by
    rw [show ((1681407221933 / 31250000000) : ℝ) = ((31250000000 / 1681407221933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0103
