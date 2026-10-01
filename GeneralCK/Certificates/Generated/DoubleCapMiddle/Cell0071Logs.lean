import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0071
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

theorem reflection_log_1_neg : (22340993 / 62500000) ≤ -Real.log (128 / 183) ∧
    -Real.log (128 / 183) ≤ (357455889 / 1000000000) := by
  have h := checkLog_sound (w := (55 / 311)) (n := 12)
    (lo := (22340993 / 62500000)) (hi := (357455889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183 / 128) = 1/(128 / 183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (22340993 / 62500000) (357455889 / 1000000000) (Real.log (183 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (183 / 128) = -Real.log (128 / 183) := by
    rw [show ((183 / 128) : ℝ) = ((128 / 183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (280785411 / 500000000) ≤ -Real.log (73 / 128) ∧
    -Real.log (73 / 128) ≤ (561570823 / 1000000000) := by
  have h := checkLog_sound (w := (55 / 201)) (n := 12)
    (lo := (280785411 / 500000000)) (hi := (561570823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 73) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 73) = 1/(73 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-561570823 / 1000000000) (-280785411 / 500000000) (Real.log (73 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8915897 / 25000000) ≤ -Real.log (2560 / 3657) ∧
    -Real.log (2560 / 3657) ≤ (356635881 / 1000000000) := by
  have h := checkLog_sound (w := (1097 / 6217)) (n := 12)
    (lo := (8915897 / 25000000)) (hi := (356635881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3657 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3657 / 2560) = 1/(2560 / 3657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8915897 / 25000000) (356635881 / 1000000000) (Real.log (3657 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3657 / 2560) = -Real.log (2560 / 3657) := by
    rw [show ((3657 / 2560) : ℝ) = ((2560 / 3657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (69939767 / 125000000) ≤ -Real.log (1463 / 2560) ∧
    -Real.log (1463 / 2560) ≤ (559518137 / 1000000000) := by
  have h := checkLog_sound (w := (1097 / 4023)) (n := 12)
    (lo := (69939767 / 125000000)) (hi := (559518137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1463) = 1/(1463 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-559518137 / 1000000000) (-69939767 / 125000000) (Real.log (1463 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (620240409 / 1000000000) ≤ -Real.log (64 / 119) ∧
    -Real.log (64 / 119) ≤ (62024041 / 100000000) := by
  have h := checkLog_sound (w := (55 / 183)) (n := 12)
    (lo := (620240409 / 1000000000)) (hi := (62024041 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119 / 64) = 1/(64 / 119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (620240409 / 1000000000) (62024041 / 100000000) (Real.log (119 / 64)) := by
  have h := reflection_log_5_neg
  have he : Real.log (119 / 64) = -Real.log (64 / 119) := by
    rw [show ((119 / 64) : ℝ) = ((64 / 119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (245207313 / 125000000) ≤ -Real.log (9 / 64) ∧
    -Real.log (9 / 64) ≤ (1961658507 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(16 / 9) = 1/(9 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1961658507 / 1000000000) (-245207313 / 125000000) (Real.log (9 / 64)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (61897911 / 100000000) ≤ -Real.log (1280 / 2377) ∧
    -Real.log (1280 / 2377) ≤ (618979111 / 1000000000) := by
  have h := checkLog_sound (w := (1097 / 3657)) (n := 12)
    (lo := (61897911 / 100000000)) (hi := (618979111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2377 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2377 / 1280) = 1/(1280 / 2377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (61897911 / 100000000) (618979111 / 1000000000) (Real.log (2377 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2377 / 1280) = -Real.log (1280 / 2377) := by
    rw [show ((2377 / 1280) : ℝ) = ((1280 / 2377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (972564601 / 500000000) ≤ -Real.log (183 / 1280) ∧
    -Real.log (183 / 1280) ≤ (389025841 / 200000000) := by
  have h := checkLog_sound (w := (137 / 503)) (n := 12)
    (lo := (279417421 / 500000000)) (hi := (558834843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 183) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 183) = 1/(183 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-389025841 / 200000000) (-972564601 / 500000000) (Real.log (183 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (491527201 / 1000000000) ≤ -Real.log (1000000 / 1634811) ∧
    -Real.log (1000000 / 1634811) ≤ (245763601 / 500000000) := by
  have h := checkLog_sound (w := (634811 / 2634811)) (n := 12)
    (lo := (491527201 / 1000000000)) (hi := (245763601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1634811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1634811 / 1000000) = 1/(1000000 / 1634811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (491527201 / 1000000000) (245763601 / 500000000) (Real.log (1634811 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1634811 / 1000000) = -Real.log (1000000 / 1634811) := by
    rw [show ((1634811 / 1000000) : ℝ) = ((1000000 / 1634811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4029361 / 4000000) ≤ -Real.log (365189 / 1000000) ∧
    -Real.log (365189 / 1000000) ≤ (251835063 / 250000000) := by
  have h := checkLog_sound (w := (134811 / 865189)) (n := 12)
    (lo := (31419307 / 100000000)) (hi := (314193071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 365189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 365189) = 1/(365189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-251835063 / 250000000) (-4029361 / 4000000) (Real.log (365189 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (123188681 / 250000000) ≤ -Real.log (1000000 / 1636819) ∧
    -Real.log (1000000 / 1636819) ≤ (19710189 / 40000000) := by
  have h := checkLog_sound (w := (636819 / 2636819)) (n := 12)
    (lo := (123188681 / 250000000)) (hi := (19710189 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1636819 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1636819 / 1000000) = 1/(1000000 / 1636819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (123188681 / 250000000) (19710189 / 40000000) (Real.log (1636819 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1636819 / 1000000) = -Real.log (1000000 / 1636819) := by
    rw [show ((1636819 / 1000000) : ℝ) = ((1000000 / 1636819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (202570789 / 200000000) ≤ -Real.log (363181 / 1000000) ∧
    -Real.log (363181 / 1000000) ≤ (1012853947 / 1000000000) := by
  have h := checkLog_sound (w := (136819 / 863181)) (n := 12)
    (lo := (63941353 / 200000000)) (hi := (159853383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 363181) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 363181) = 1/(363181 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1012853947 / 1000000000) (-202570789 / 200000000) (Real.log (363181 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (408565629 / 1000000000) ≤ -Real.log (500000 / 752329) ∧
    -Real.log (500000 / 752329) ≤ (40856563 / 100000000) := by
  have h := checkLog_sound (w := (252329 / 1252329)) (n := 12)
    (lo := (408565629 / 1000000000)) (hi := (40856563 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((752329 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(752329 / 500000) = 1/(500000 / 752329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (408565629 / 1000000000) (40856563 / 100000000) (Real.log (752329 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (752329 / 500000) = -Real.log (500000 / 752329) := by
    rw [show ((752329 / 500000) : ℝ) = ((500000 / 752329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (140501369 / 200000000) ≤ -Real.log (247671 / 500000) ∧
    -Real.log (247671 / 500000) ≤ (702506847 / 1000000000) := by
  have h := checkLog_sound (w := (2329 / 497671)) (n := 12)
    (lo := (1871933 / 200000000)) (hi := (4679833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 247671) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 247671) = 1/(247671 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-702506847 / 1000000000) (-140501369 / 200000000) (Real.log (247671 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (102471497 / 250000000) ≤ -Real.log (500000 / 753323) ∧
    -Real.log (500000 / 753323) ≤ (409885989 / 1000000000) := by
  have h := checkLog_sound (w := (253323 / 1253323)) (n := 12)
    (lo := (102471497 / 250000000)) (hi := (409885989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753323 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753323 / 500000) = 1/(500000 / 753323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (102471497 / 250000000) (409885989 / 1000000000) (Real.log (753323 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (753323 / 500000) = -Real.log (500000 / 753323) := by
    rw [show ((753323 / 500000) : ℝ) = ((500000 / 753323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (706528309 / 1000000000) ≤ -Real.log (246677 / 500000) ∧
    -Real.log (246677 / 500000) ≤ (706528311 / 1000000000) := by
  have h := checkLog_sound (w := (3323 / 496677)) (n := 12)
    (lo := (13381129 / 1000000000)) (hi := (1338113 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 246677) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 246677) = 1/(246677 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-706528311 / 1000000000) (-706528309 / 1000000000) (Real.log (246677 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1498867451 / 1000000000) ≤ -Real.log (500000000000 / 2238308108951) ∧
    -Real.log (500000000000 / 2238308108951) ≤ (749433727 / 500000000) := by
  have h := checkLog_sound (w := (238308108951 / 4238308108951)) (n := 12)
    (lo := (112573091 / 1000000000)) (hi := (28143273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2238308108951 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2238308108951 / 2000000000000) = 1/(500000000000 / 2238308108951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1498867451 / 1000000000) (749433727 / 500000000) (Real.log (2238308108951 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2238308108951 / 500000000000) = -Real.log (500000000000 / 2238308108951) := by
    rw [show ((2238308108951 / 500000000000) : ℝ) = ((500000000000 / 2238308108951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1505608669 / 1000000000) ≤ -Real.log (100000000000 / 450689601053) ∧
    -Real.log (100000000000 / 450689601053) ≤ (47050271 / 31250000) := by
  have h := checkLog_sound (w := (50689601053 / 850689601053)) (n := 12)
    (lo := (119314309 / 1000000000)) (hi := (11931431 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450689601053 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(450689601053 / 400000000000) = 1/(100000000000 / 450689601053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1505608669 / 1000000000) (47050271 / 31250000) (Real.log (450689601053 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (450689601053 / 100000000000) = -Real.log (100000000000 / 450689601053) := by
    rw [show ((450689601053 / 100000000000) : ℝ) = ((100000000000 / 450689601053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (44442899 / 40000000) ≤ -Real.log (500000000000 / 1518807207949) ∧
    -Real.log (500000000000 / 1518807207949) ≤ (1111072477 / 1000000000) := by
  have h := checkLog_sound (w := (518807207949 / 2518807207949)) (n := 12)
    (lo := (83585059 / 200000000)) (hi := (26120331 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1518807207949 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1518807207949 / 1000000000000) = 1/(500000000000 / 1518807207949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (44442899 / 40000000) (1111072477 / 1000000000) (Real.log (1518807207949 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1518807207949 / 500000000000) = -Real.log (500000000000 / 1518807207949) := by
    rw [show ((1518807207949 / 500000000000) : ℝ) = ((500000000000 / 1518807207949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1116414297 / 1000000000) ≤ -Real.log (125000000000 / 381735528647) ∧
    -Real.log (125000000000 / 381735528647) ≤ (1116414299 / 1000000000) := by
  have h := checkLog_sound (w := (131735528647 / 631735528647)) (n := 12)
    (lo := (423267117 / 1000000000)) (hi := (211633559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381735528647 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(381735528647 / 250000000000) = 1/(125000000000 / 381735528647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1116414297 / 1000000000) (1116414299 / 1000000000) (Real.log (381735528647 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (381735528647 / 125000000000) = -Real.log (125000000000 / 381735528647) := by
    rw [show ((381735528647 / 125000000000) : ℝ) = ((125000000000 / 381735528647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0071
