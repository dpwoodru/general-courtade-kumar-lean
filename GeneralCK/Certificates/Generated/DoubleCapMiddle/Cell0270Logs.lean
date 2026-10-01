import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0270
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

theorem reflection_log_1_neg : (116856251 / 500000000) ≤ -Real.log (1280 / 1617) ∧
    -Real.log (1280 / 1617) ≤ (233712503 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 2897)) (n := 12)
    (lo := (116856251 / 500000000)) (hi := (233712503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1617 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1617 / 1280) = 1/(1280 / 1617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (116856251 / 500000000) (233712503 / 1000000000) (Real.log (1617 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1617 / 1280) = -Real.log (1280 / 1617) := by
    rw [show ((1617 / 1280) : ℝ) = ((1280 / 1617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (152774537 / 500000000) ≤ -Real.log (943 / 1280) ∧
    -Real.log (943 / 1280) ≤ (12221963 / 40000000) := by
  have h := checkLog_sound (w := (337 / 2223)) (n := 12)
    (lo := (152774537 / 500000000)) (hi := (12221963 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 943) = 1/(943 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12221963 / 40000000) (-152774537 / 500000000) (Real.log (943 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (233248573 / 1000000000) ≤ -Real.log (1024 / 1293) ∧
    -Real.log (1024 / 1293) ≤ (116624287 / 500000000) := by
  have h := checkLog_sound (w := (269 / 2317)) (n := 12)
    (lo := (233248573 / 1000000000)) (hi := (116624287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1293 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1293 / 1024) = 1/(1024 / 1293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (233248573 / 1000000000) (116624287 / 500000000) (Real.log (1293 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1293 / 1024) = -Real.log (1024 / 1293) := by
    rw [show ((1293 / 1024) : ℝ) = ((1024 / 1293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (38094257 / 125000000) ≤ -Real.log (755 / 1024) ∧
    -Real.log (755 / 1024) ≤ (304754057 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 1779)) (n := 12)
    (lo := (38094257 / 125000000)) (hi := (304754057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 755) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 755) = 1/(755 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-304754057 / 1000000000) (-38094257 / 125000000) (Real.log (755 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (16920739 / 40000000) ≤ -Real.log (640 / 977) ∧
    -Real.log (640 / 977) ≤ (105754619 / 250000000) := by
  have h := checkLog_sound (w := (337 / 1617)) (n := 12)
    (lo := (16920739 / 40000000)) (hi := (105754619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977 / 640) = 1/(640 / 977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (16920739 / 40000000) (105754619 / 250000000) (Real.log (977 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (977 / 640) = -Real.log (640 / 977) := by
    rw [show ((977 / 640) : ℝ) = ((640 / 977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (74773537 / 100000000) ≤ -Real.log (303 / 640) ∧
    -Real.log (303 / 640) ≤ (186933843 / 250000000) := by
  have h := checkLog_sound (w := (17 / 623)) (n := 12)
    (lo := (5458819 / 100000000)) (hi := (54588191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 303) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 303) = 1/(303 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-186933843 / 250000000) (-74773537 / 100000000) (Real.log (303 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (105562631 / 250000000) ≤ -Real.log (512 / 781) ∧
    -Real.log (512 / 781) ≤ (16890021 / 40000000) := by
  have h := checkLog_sound (w := (269 / 1293)) (n := 12)
    (lo := (105562631 / 250000000)) (hi := (16890021 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((781 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(781 / 512) = 1/(512 / 781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (105562631 / 250000000) (16890021 / 40000000) (Real.log (781 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (781 / 512) = -Real.log (512 / 781) := by
    rw [show ((781 / 512) : ℝ) = ((512 / 781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (745263181 / 1000000000) ≤ -Real.log (243 / 512) ∧
    -Real.log (243 / 512) ≤ (745263183 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 499)) (n := 12)
    (lo := (52116001 / 1000000000)) (hi := (26058001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 243) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 243) = 1/(243 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-745263183 / 1000000000) (-745263181 / 1000000000) (Real.log (243 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (319440153 / 1000000000) ≤ -Real.log (1000000 / 1376357) ∧
    -Real.log (1000000 / 1376357) ≤ (159720077 / 500000000) := by
  have h := checkLog_sound (w := (376357 / 2376357)) (n := 12)
    (lo := (319440153 / 1000000000)) (hi := (159720077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1376357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1376357 / 1000000) = 1/(1000000 / 1376357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (319440153 / 1000000000) (159720077 / 500000000) (Real.log (1376357 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1376357 / 1000000) = -Real.log (1000000 / 1376357) := by
    rw [show ((1376357 / 1000000) : ℝ) = ((1000000 / 1376357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (472177189 / 1000000000) ≤ -Real.log (623643 / 1000000) ∧
    -Real.log (623643 / 1000000) ≤ (47217719 / 100000000) := by
  have h := checkLog_sound (w := (376357 / 1623643)) (n := 12)
    (lo := (472177189 / 1000000000)) (hi := (47217719 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 623643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 623643) = 1/(623643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-47217719 / 100000000) (-472177189 / 1000000000) (Real.log (623643 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (160034213 / 500000000) ≤ -Real.log (500000 / 688611) ∧
    -Real.log (500000 / 688611) ≤ (320068427 / 1000000000) := by
  have h := checkLog_sound (w := (188611 / 1188611)) (n := 12)
    (lo := (160034213 / 500000000)) (hi := (320068427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688611 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688611 / 500000) = 1/(500000 / 688611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (160034213 / 500000000) (320068427 / 1000000000) (Real.log (688611 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (688611 / 500000) = -Real.log (500000 / 688611) := by
    rw [show ((688611 / 500000) : ℝ) = ((500000 / 688611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (473565163 / 1000000000) ≤ -Real.log (311389 / 500000) ∧
    -Real.log (311389 / 500000) ≤ (118391291 / 250000000) := by
  have h := checkLog_sound (w := (188611 / 811389)) (n := 12)
    (lo := (473565163 / 1000000000)) (hi := (118391291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 311389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 311389) = 1/(311389 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-118391291 / 250000000) (-473565163 / 1000000000) (Real.log (311389 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (244493999 / 1000000000) ≤ -Real.log (40000 / 51079) ∧
    -Real.log (40000 / 51079) ≤ (122247 / 500000) := by
  have h := checkLog_sound (w := (11079 / 91079)) (n := 12)
    (lo := (244493999 / 1000000000)) (hi := (122247 / 500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51079 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51079 / 40000) = 1/(40000 / 51079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (244493999 / 1000000000) (122247 / 500000) (Real.log (51079 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (51079 / 40000) = -Real.log (40000 / 51079) := by
    rw [show ((51079 / 40000) : ℝ) = ((40000 / 51079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (324311479 / 1000000000) ≤ -Real.log (28921 / 40000) ∧
    -Real.log (28921 / 40000) ≤ (8107787 / 25000000) := by
  have h := checkLog_sound (w := (11079 / 68921)) (n := 12)
    (lo := (324311479 / 1000000000)) (hi := (8107787 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 28921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 28921) = 1/(28921 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-8107787 / 25000000) (-324311479 / 1000000000) (Real.log (28921 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (24503341 / 100000000) ≤ -Real.log (31250 / 39927) ∧
    -Real.log (31250 / 39927) ≤ (245033411 / 1000000000) := by
  have h := checkLog_sound (w := (8677 / 71177)) (n := 12)
    (lo := (24503341 / 100000000)) (hi := (245033411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39927 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39927 / 31250) = 1/(31250 / 39927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (24503341 / 100000000) (245033411 / 1000000000) (Real.log (39927 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (39927 / 31250) = -Real.log (31250 / 39927) := by
    rw [show ((39927 / 31250) : ℝ) = ((31250 / 39927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (162632437 / 500000000) ≤ -Real.log (22573 / 31250) ∧
    -Real.log (22573 / 31250) ≤ (2602119 / 8000000) := by
  have h := checkLog_sound (w := (8677 / 53823)) (n := 12)
    (lo := (162632437 / 500000000)) (hi := (2602119 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 22573) = 1/(22573 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2602119 / 8000000) (-162632437 / 500000000) (Real.log (22573 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (395808671 / 500000000) ≤ -Real.log (500000000000 / 1103481478987) ∧
    -Real.log (500000000000 / 1103481478987) ≤ (12369021 / 15625000) := by
  have h := checkLog_sound (w := (103481478987 / 2103481478987)) (n := 12)
    (lo := (49235081 / 500000000)) (hi := (98470163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1103481478987 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1103481478987 / 1000000000000) = 1/(500000000000 / 1103481478987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (395808671 / 500000000) (12369021 / 15625000) (Real.log (1103481478987 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1103481478987 / 500000000000) = -Real.log (500000000000 / 1103481478987) := by
    rw [show ((1103481478987 / 500000000000) : ℝ) = ((500000000000 / 1103481478987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (79363359 / 100000000) ≤ -Real.log (50000000000 / 110570861527) ∧
    -Real.log (50000000000 / 110570861527) ≤ (99204199 / 125000000) := by
  have h := checkLog_sound (w := (10570861527 / 210570861527)) (n := 12)
    (lo := (10048641 / 100000000)) (hi := (100486411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110570861527 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(110570861527 / 100000000000) = 1/(50000000000 / 110570861527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (79363359 / 100000000) (99204199 / 125000000) (Real.log (110570861527 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (110570861527 / 50000000000) = -Real.log (50000000000 / 110570861527) := by
    rw [show ((110570861527 / 50000000000) : ℝ) = ((50000000000 / 110570861527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (284402739 / 500000000) ≤ -Real.log (250000000000 / 441539020089) ∧
    -Real.log (250000000000 / 441539020089) ≤ (568805479 / 1000000000) := by
  have h := checkLog_sound (w := (191539020089 / 691539020089)) (n := 12)
    (lo := (284402739 / 500000000)) (hi := (568805479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441539020089 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441539020089 / 250000000000) = 1/(250000000000 / 441539020089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (284402739 / 500000000) (568805479 / 1000000000) (Real.log (441539020089 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (441539020089 / 250000000000) = -Real.log (250000000000 / 441539020089) := by
    rw [show ((441539020089 / 250000000000) : ℝ) = ((250000000000 / 441539020089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (142574571 / 250000000) ≤ -Real.log (500000000000 / 884397288797) ∧
    -Real.log (500000000000 / 884397288797) ≤ (114059657 / 200000000) := by
  have h := checkLog_sound (w := (384397288797 / 1384397288797)) (n := 12)
    (lo := (142574571 / 250000000)) (hi := (114059657 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((884397288797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(884397288797 / 500000000000) = 1/(500000000000 / 884397288797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (142574571 / 250000000) (114059657 / 200000000) (Real.log (884397288797 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (884397288797 / 500000000000) = -Real.log (500000000000 / 884397288797) := by
    rw [show ((884397288797 / 500000000000) : ℝ) = ((500000000000 / 884397288797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0270
