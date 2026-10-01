import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0133
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

theorem reflection_log_1_neg : (305299409 / 1000000000) ≤ -Real.log (1280 / 1737) ∧
    -Real.log (1280 / 1737) ≤ (30529941 / 100000000) := by
  have h := checkLog_sound (w := (457 / 3017)) (n := 12)
    (lo := (305299409 / 1000000000)) (hi := (30529941 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1737 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1737 / 1280) = 1/(1280 / 1737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (305299409 / 1000000000) (30529941 / 100000000) (Real.log (1737 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1737 / 1280) = -Real.log (1280 / 1737) := by
    rw [show ((1737 / 1280) : ℝ) = ((1280 / 1737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (110414789 / 250000000) ≤ -Real.log (823 / 1280) ∧
    -Real.log (823 / 1280) ≤ (441659157 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 2103)) (n := 12)
    (lo := (110414789 / 250000000)) (hi := (441659157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 823) = 1/(823 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-441659157 / 1000000000) (-110414789 / 250000000) (Real.log (823 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (152217739 / 500000000) ≤ -Real.log (2560 / 3471) ∧
    -Real.log (2560 / 3471) ≤ (304435479 / 1000000000) := by
  have h := checkLog_sound (w := (911 / 6031)) (n := 12)
    (lo := (152217739 / 500000000)) (hi := (304435479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3471 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3471 / 2560) = 1/(2560 / 3471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (152217739 / 500000000) (304435479 / 1000000000) (Real.log (3471 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3471 / 2560) = -Real.log (2560 / 3471) := by
    rw [show ((3471 / 2560) : ℝ) = ((2560 / 3471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (219919107 / 500000000) ≤ -Real.log (1649 / 2560) ∧
    -Real.log (1649 / 2560) ≤ (87967643 / 200000000) := by
  have h := checkLog_sound (w := (911 / 4209)) (n := 12)
    (lo := (219919107 / 500000000)) (hi := (87967643 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1649) = 1/(1649 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-87967643 / 200000000) (-219919107 / 500000000) (Real.log (1649 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (538866283 / 1000000000) ≤ -Real.log (640 / 1097) ∧
    -Real.log (640 / 1097) ≤ (134716571 / 250000000) := by
  have h := checkLog_sound (w := (457 / 1737)) (n := 12)
    (lo := (538866283 / 1000000000)) (hi := (134716571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097 / 640) = 1/(640 / 1097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (538866283 / 1000000000) (134716571 / 250000000) (Real.log (1097 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1097 / 640) = -Real.log (640 / 1097) := by
    rw [show ((1097 / 640) : ℝ) = ((640 / 1097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (625991011 / 500000000) ≤ -Real.log (183 / 640) ∧
    -Real.log (183 / 640) ≤ (156497753 / 125000000) := by
  have h := checkLog_sound (w := (137 / 503)) (n := 12)
    (lo := (279417421 / 500000000)) (hi := (558834843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 183) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 183) = 1/(183 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-156497753 / 125000000) (-625991011 / 500000000) (Real.log (183 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (268748991 / 500000000) ≤ -Real.log (1280 / 2191) ∧
    -Real.log (1280 / 2191) ≤ (537497983 / 1000000000) := by
  have h := checkLog_sound (w := (911 / 3471)) (n := 12)
    (lo := (268748991 / 500000000)) (hi := (537497983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2191 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2191 / 1280) = 1/(1280 / 2191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (268748991 / 500000000) (537497983 / 1000000000) (Real.log (2191 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2191 / 1280) = -Real.log (1280 / 2191) := by
    rw [show ((2191 / 1280) : ℝ) = ((1280 / 2191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (155477339 / 125000000) ≤ -Real.log (369 / 1280) ∧
    -Real.log (369 / 1280) ≤ (621909357 / 500000000) := by
  have h := checkLog_sound (w := (271 / 1009)) (n := 12)
    (lo := (137667883 / 250000000)) (hi := (550671533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 369) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 369) = 1/(369 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-621909357 / 500000000) (-155477339 / 125000000) (Real.log (369 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (208381193 / 500000000) ≤ -Real.log (500000 / 758521) ∧
    -Real.log (500000 / 758521) ≤ (416762387 / 1000000000) := by
  have h := checkLog_sound (w := (258521 / 1258521)) (n := 12)
    (lo := (208381193 / 500000000)) (hi := (416762387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((758521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(758521 / 500000) = 1/(500000 / 758521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (208381193 / 500000000) (416762387 / 1000000000) (Real.log (758521 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (758521 / 500000) = -Real.log (500000 / 758521) := by
    rw [show ((758521 / 500000) : ℝ) = ((500000 / 758521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (145565117 / 200000000) ≤ -Real.log (241479 / 500000) ∧
    -Real.log (241479 / 500000) ≤ (727825587 / 1000000000) := by
  have h := checkLog_sound (w := (8521 / 491479)) (n := 12)
    (lo := (6935681 / 200000000)) (hi := (17339203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 241479) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 241479) = 1/(241479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-727825587 / 1000000000) (-145565117 / 200000000) (Real.log (241479 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (10449133 / 25000000) ≤ -Real.log (250000 / 379717) ∧
    -Real.log (250000 / 379717) ≤ (417965321 / 1000000000) := by
  have h := checkLog_sound (w := (129717 / 629717)) (n := 12)
    (lo := (10449133 / 25000000)) (hi := (417965321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379717 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(379717 / 250000) = 1/(250000 / 379717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (10449133 / 25000000) (417965321 / 1000000000) (Real.log (379717 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (379717 / 250000) = -Real.log (250000 / 379717) := by
    rw [show ((379717 / 250000) : ℝ) = ((250000 / 379717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (731613617 / 1000000000) ≤ -Real.log (120283 / 250000) ∧
    -Real.log (120283 / 250000) ≤ (731613619 / 1000000000) := by
  have h := checkLog_sound (w := (4717 / 245283)) (n := 12)
    (lo := (38466437 / 1000000000)) (hi := (19233219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 120283) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 120283) = 1/(120283 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-731613619 / 1000000000) (-731613617 / 1000000000) (Real.log (120283 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (41584021 / 125000000) ≤ -Real.log (100000 / 139469) ∧
    -Real.log (100000 / 139469) ≤ (332672169 / 1000000000) := by
  have h := checkLog_sound (w := (39469 / 239469)) (n := 12)
    (lo := (41584021 / 125000000)) (hi := (332672169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139469 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139469 / 100000) = 1/(100000 / 139469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (41584021 / 125000000) (332672169 / 1000000000) (Real.log (139469 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (139469 / 100000) = -Real.log (100000 / 139469) := by
    rw [show ((139469 / 100000) : ℝ) = ((100000 / 139469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (100402911 / 200000000) ≤ -Real.log (60531 / 100000) ∧
    -Real.log (60531 / 100000) ≤ (125503639 / 250000000) := by
  have h := checkLog_sound (w := (39469 / 160531)) (n := 12)
    (lo := (100402911 / 200000000)) (hi := (125503639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 60531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 60531) = 1/(60531 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-125503639 / 250000000) (-100402911 / 200000000) (Real.log (60531 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (333829461 / 1000000000) ≤ -Real.log (200000 / 279261) ∧
    -Real.log (200000 / 279261) ≤ (166914731 / 500000000) := by
  have h := checkLog_sound (w := (79261 / 479261)) (n := 12)
    (lo := (333829461 / 1000000000)) (hi := (166914731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279261 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279261 / 200000) = 1/(200000 / 279261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (333829461 / 1000000000) (166914731 / 500000000) (Real.log (279261 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (279261 / 200000) = -Real.log (200000 / 279261) := by
    rw [show ((279261 / 200000) : ℝ) = ((200000 / 279261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (20187447 / 40000000) ≤ -Real.log (120739 / 200000) ∧
    -Real.log (120739 / 200000) ≤ (15771443 / 31250000) := by
  have h := checkLog_sound (w := (79261 / 320739)) (n := 12)
    (lo := (20187447 / 40000000)) (hi := (15771443 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 120739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 120739) = 1/(120739 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-15771443 / 31250000) (-20187447 / 40000000) (Real.log (120739 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1144587971 / 1000000000) ≤ -Real.log (125000000000 / 392643356151) ∧
    -Real.log (125000000000 / 392643356151) ≤ (1144587973 / 1000000000) := by
  have h := checkLog_sound (w := (142643356151 / 642643356151)) (n := 12)
    (lo := (451440791 / 1000000000)) (hi := (56430099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392643356151 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(392643356151 / 250000000000) = 1/(125000000000 / 392643356151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1144587971 / 1000000000) (1144587973 / 1000000000) (Real.log (392643356151 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (392643356151 / 125000000000) = -Real.log (125000000000 / 392643356151) := by
    rw [show ((392643356151 / 125000000000) : ℝ) = ((125000000000 / 392643356151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (574789469 / 500000000) ≤ -Real.log (250000000000 / 789215849289) ∧
    -Real.log (250000000000 / 789215849289) ≤ (57478947 / 50000000) := by
  have h := checkLog_sound (w := (289215849289 / 1289215849289)) (n := 12)
    (lo := (228215879 / 500000000)) (hi := (456431759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789215849289 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(789215849289 / 500000000000) = 1/(250000000000 / 789215849289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (574789469 / 500000000) (57478947 / 50000000) (Real.log (789215849289 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (789215849289 / 250000000000) = -Real.log (250000000000 / 789215849289) := by
    rw [show ((789215849289 / 250000000000) : ℝ) = ((250000000000 / 789215849289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (834686723 / 1000000000) ≤ -Real.log (125000000000 / 288011514761) ∧
    -Real.log (125000000000 / 288011514761) ≤ (33387469 / 40000000) := by
  have h := checkLog_sound (w := (38011514761 / 538011514761)) (n := 12)
    (lo := (141539543 / 1000000000)) (hi := (17692443 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288011514761 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(288011514761 / 250000000000) = 1/(125000000000 / 288011514761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (834686723 / 1000000000) (33387469 / 40000000) (Real.log (288011514761 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (288011514761 / 125000000000) = -Real.log (125000000000 / 288011514761) := by
    rw [show ((288011514761 / 125000000000) : ℝ) = ((125000000000 / 288011514761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (209628909 / 250000000) ≤ -Real.log (500000000000 / 1156465599351) ∧
    -Real.log (500000000000 / 1156465599351) ≤ (419257819 / 500000000) := by
  have h := checkLog_sound (w := (156465599351 / 2156465599351)) (n := 12)
    (lo := (18171057 / 125000000)) (hi := (145368457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1156465599351 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1156465599351 / 1000000000000) = 1/(500000000000 / 1156465599351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (209628909 / 250000000) (419257819 / 500000000) (Real.log (1156465599351 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1156465599351 / 500000000000) = -Real.log (500000000000 / 1156465599351) := by
    rw [show ((1156465599351 / 500000000000) : ℝ) = ((500000000000 / 1156465599351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0133
