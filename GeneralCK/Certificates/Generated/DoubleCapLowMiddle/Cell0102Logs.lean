import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0102
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

theorem reflection_log_1_neg : (1073647 / 1600000) ≤ -Real.log (160 / 313) ∧
    -Real.log (160 / 313) ≤ (5242417 / 7812500) := by
  have h := checkLog_sound (w := (153 / 473)) (n := 12)
    (lo := (1073647 / 1600000)) (hi := (5242417 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313 / 160) = 1/(160 / 313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (1073647 / 1600000) (5242417 / 7812500) (Real.log (313 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (313 / 160) = -Real.log (160 / 313) := by
    rw [show ((313 / 160) : ℝ) = ((160 / 313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3129263663 / 1000000000) ≤ -Real.log (7 / 160) ∧
    -Real.log (7 / 160) ≤ (782315917 / 250000000) := by
  have h := checkLog_sound (w := (3 / 17)) (n := 12)
    (lo := (356674943 / 1000000000)) (hi := (2786523 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 7) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10 / 7) = 1/(7 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-782315917 / 250000000) (-3129263663 / 1000000000) (Real.log (7 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (33541983 / 50000000) ≤ -Real.log (51200 / 100141) ∧
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


theorem reflection_log_3 : Bounds (33541983 / 50000000) (670839661 / 1000000000) (Real.log (100141 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100141 / 51200) = -Real.log (51200 / 100141) := by
    rw [show ((100141 / 51200) : ℝ) = ((51200 / 100141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (780204323 / 250000000) ≤ -Real.log (2259 / 51200) ∧
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


theorem reflection_log_4 : Bounds (-3120817297 / 1000000000) (-780204323 / 250000000) (Real.log (2259 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (324205643 / 500000000) ≤ -Real.log (80 / 153) ∧
    -Real.log (80 / 153) ≤ (648411287 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 233)) (n := 12)
    (lo := (324205643 / 500000000)) (hi := (648411287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153 / 80) = 1/(80 / 153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (324205643 / 500000000) (648411287 / 1000000000) (Real.log (153 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (153 / 80) = -Real.log (80 / 153) := by
    rw [show ((153 / 80) : ℝ) = ((80 / 153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2436116483 / 1000000000) ≤ -Real.log (7 / 80) ∧
    -Real.log (7 / 80) ≤ (2436116487 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 17)) (n := 12)
    (lo := (356674943 / 1000000000)) (hi := (2786523 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 7) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(10 / 7) = 1/(7 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2436116487 / 1000000000) (-2436116483 / 1000000000) (Real.log (7 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (648023139 / 1000000000) ≤ -Real.log (25600 / 48941) ∧
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


theorem reflection_log_7 : Bounds (648023139 / 1000000000) (32401157 / 50000000) (Real.log (48941 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (48941 / 25600) = -Real.log (25600 / 48941) := by
    rw [show ((48941 / 25600) : ℝ) = ((25600 / 48941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (75864691 / 31250000) ≤ -Real.log (2259 / 25600) ∧
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


theorem reflection_log_8 : Bounds (-606917529 / 250000000) (-75864691 / 31250000) (Real.log (2259 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (674915997 / 1000000000) ≤ -Real.log (250000 / 490967) ∧
    -Real.log (250000 / 490967) ≤ (337457999 / 500000000) := by
  have h := checkLog_sound (w := (240967 / 740967)) (n := 12)
    (lo := (674915997 / 1000000000)) (hi := (337457999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490967 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(490967 / 250000) = 1/(250000 / 490967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (674915997 / 1000000000) (337457999 / 500000000) (Real.log (490967 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (490967 / 250000) = -Real.log (250000 / 490967) := by
    rw [show ((490967 / 250000) : ℝ) = ((250000 / 490967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3320576377 / 1000000000) ≤ -Real.log (9033 / 250000) ∧
    -Real.log (9033 / 250000) ≤ (1660288191 / 500000000) := by
  have h := checkLog_sound (w := (3296 / 12329)) (n := 12)
    (lo := (547987657 / 1000000000)) (hi := (273993829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9033) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 9033) = 1/(9033 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1660288191 / 500000000) (-3320576377 / 1000000000) (Real.log (9033 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (337530809 / 500000000) ≤ -Real.log (500000 / 982077) ∧
    -Real.log (500000 / 982077) ≤ (675061619 / 1000000000) := by
  have h := checkLog_sound (w := (482077 / 1482077)) (n := 12)
    (lo := (337530809 / 500000000)) (hi := (675061619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982077 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982077 / 500000) = 1/(500000 / 982077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (337530809 / 500000000) (675061619 / 1000000000) (Real.log (982077 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (982077 / 500000) = -Real.log (500000 / 982077) := by
    rw [show ((982077 / 500000) : ℝ) = ((500000 / 982077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3328523291 / 1000000000) ≤ -Real.log (17923 / 500000) ∧
    -Real.log (17923 / 500000) ≤ (104016353 / 31250000) := by
  have h := checkLog_sound (w := (13327 / 49173)) (n := 12)
    (lo := (555934571 / 1000000000)) (hi := (138983643 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17923) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 17923) = 1/(17923 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-104016353 / 31250000) (-3328523291 / 1000000000) (Real.log (17923 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (13494633 / 20000000) ≤ -Real.log (500000 / 981753) ∧
    -Real.log (500000 / 981753) ≤ (674731651 / 1000000000) := by
  have h := checkLog_sound (w := (481753 / 1481753)) (n := 12)
    (lo := (13494633 / 20000000)) (hi := (674731651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981753 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981753 / 500000) = 1/(500000 / 981753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (13494633 / 20000000) (674731651 / 1000000000) (Real.log (981753 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (981753 / 500000) = -Real.log (500000 / 981753) := by
    rw [show ((981753 / 500000) : ℝ) = ((500000 / 981753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3310607413 / 1000000000) ≤ -Real.log (18247 / 500000) ∧
    -Real.log (18247 / 500000) ≤ (1655303709 / 500000000) := by
  have h := checkLog_sound (w := (13003 / 49497)) (n := 12)
    (lo := (538018693 / 1000000000)) (hi := (269009347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18247) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18247) = 1/(18247 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1655303709 / 500000000) (-3310607413 / 1000000000) (Real.log (18247 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (674881371 / 1000000000) ≤ -Real.log (5000 / 9819) ∧
    -Real.log (5000 / 9819) ≤ (168720343 / 250000000) := by
  have h := checkLog_sound (w := (4819 / 14819)) (n := 12)
    (lo := (674881371 / 1000000000)) (hi := (168720343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9819 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9819 / 5000) = 1/(5000 / 9819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (674881371 / 1000000000) (168720343 / 250000000) (Real.log (9819 / 5000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (9819 / 5000) = -Real.log (5000 / 9819) := by
    rw [show ((9819 / 5000) : ℝ) = ((5000 / 9819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3318696157 / 1000000000) ≤ -Real.log (181 / 5000) ∧
    -Real.log (181 / 5000) ≤ (1659348081 / 500000000) := by
  have h := checkLog_sound (w := (263 / 987)) (n := 12)
    (lo := (546107437 / 1000000000)) (hi := (273053719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 362) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(625 / 362) = 1/(181 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1659348081 / 500000000) (-3318696157 / 1000000000) (Real.log (181 / 5000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1997746187 / 500000000) ≤ -Real.log (500000000000 / 27176298018377) ∧
    -Real.log (500000000000 / 27176298018377) ≤ (199774619 / 50000000) := by
  have h := checkLog_sound (w := (11176298018377 / 43176298018377)) (n := 12)
    (lo := (264878237 / 500000000)) (hi := (21190259 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27176298018377 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(27176298018377 / 16000000000000) = 1/(500000000000 / 27176298018377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1997746187 / 500000000) (199774619 / 50000000) (Real.log (27176298018377 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (27176298018377 / 500000000000) = -Real.log (500000000000 / 27176298018377) := by
    rw [show ((27176298018377 / 500000000000) : ℝ) = ((500000000000 / 27176298018377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4003584909 / 1000000000) ≤ -Real.log (62500000000 / 3424639429783) ∧
    -Real.log (62500000000 / 3424639429783) ≤ (800716983 / 200000000) := by
  have h := checkLog_sound (w := (1424639429783 / 5424639429783)) (n := 12)
    (lo := (537849009 / 1000000000)) (hi := (53784901 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3424639429783 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3424639429783 / 2000000000000) = 1/(62500000000 / 3424639429783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4003584909 / 1000000000) (800716983 / 200000000) (Real.log (3424639429783 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3424639429783 / 62500000000) = -Real.log (62500000000 / 3424639429783) := by
    rw [show ((3424639429783 / 62500000000) : ℝ) = ((62500000000 / 3424639429783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3985339063 / 1000000000) ≤ -Real.log (125000000000 / 6725441168411) ∧
    -Real.log (125000000000 / 6725441168411) ≤ (3985339069 / 1000000000) := by
  have h := checkLog_sound (w := (2725441168411 / 10725441168411)) (n := 12)
    (lo := (519603163 / 1000000000)) (hi := (129900791 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6725441168411 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6725441168411 / 4000000000000) = 1/(125000000000 / 6725441168411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3985339063 / 1000000000) (3985339069 / 1000000000) (Real.log (6725441168411 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6725441168411 / 125000000000) = -Real.log (125000000000 / 6725441168411) := by
    rw [show ((6725441168411 / 125000000000) : ℝ) = ((125000000000 / 6725441168411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3993577529 / 1000000000) ≤ -Real.log (250000000000 / 13562154696133) ∧
    -Real.log (250000000000 / 13562154696133) ≤ (798715507 / 200000000) := by
  have h := checkLog_sound (w := (5562154696133 / 21562154696133)) (n := 12)
    (lo := (527841629 / 1000000000)) (hi := (52784163 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13562154696133 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13562154696133 / 8000000000000) = 1/(250000000000 / 13562154696133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3993577529 / 1000000000) (798715507 / 200000000) (Real.log (13562154696133 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (13562154696133 / 250000000000) = -Real.log (250000000000 / 13562154696133) := by
    rw [show ((13562154696133 / 250000000000) : ℝ) = ((250000000000 / 13562154696133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0102
