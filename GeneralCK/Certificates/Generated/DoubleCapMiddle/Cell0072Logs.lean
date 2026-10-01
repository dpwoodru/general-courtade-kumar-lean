import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0072
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

theorem reflection_log_1_neg : (8915897 / 25000000) ≤ -Real.log (2560 / 3657) ∧
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


theorem reflection_log_1 : Bounds (8915897 / 25000000) (356635881 / 1000000000) (Real.log (3657 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3657 / 2560) = -Real.log (2560 / 3657) := by
    rw [show ((3657 / 2560) : ℝ) = ((2560 / 3657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (69939767 / 125000000) ≤ -Real.log (1463 / 2560) ∧
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


theorem reflection_log_2 : Bounds (-559518137 / 1000000000) (-69939767 / 125000000) (Real.log (1463 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (355815199 / 1000000000) ≤ -Real.log (1280 / 1827) ∧
    -Real.log (1280 / 1827) ≤ (444769 / 1250000) := by
  have h := checkLog_sound (w := (547 / 3107)) (n := 12)
    (lo := (355815199 / 1000000000)) (hi := (444769 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1827 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1827 / 1280) = 1/(1280 / 1827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (355815199 / 1000000000) (444769 / 1250000) (Real.log (1827 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1827 / 1280) = -Real.log (1280 / 1827) := by
    rw [show ((1827 / 1280) : ℝ) = ((1280 / 1827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (111493931 / 200000000) ≤ -Real.log (733 / 1280) ∧
    -Real.log (733 / 1280) ≤ (69683707 / 125000000) := by
  have h := checkLog_sound (w := (547 / 2013)) (n := 12)
    (lo := (111493931 / 200000000)) (hi := (69683707 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 733) = 1/(733 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-69683707 / 125000000) (-111493931 / 200000000) (Real.log (733 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (61897911 / 100000000) ≤ -Real.log (1280 / 2377) ∧
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


theorem reflection_log_5 : Bounds (61897911 / 100000000) (618979111 / 1000000000) (Real.log (2377 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2377 / 1280) = -Real.log (1280 / 2377) := by
    rw [show ((2377 / 1280) : ℝ) = ((1280 / 2377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (972564601 / 500000000) ≤ -Real.log (183 / 1280) ∧
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


theorem reflection_log_6 : Bounds (-389025841 / 200000000) (-972564601 / 500000000) (Real.log (183 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (308858109 / 500000000) ≤ -Real.log (640 / 1187) ∧
    -Real.log (640 / 1187) ≤ (617716219 / 1000000000) := by
  have h := checkLog_sound (w := (547 / 1827)) (n := 12)
    (lo := (308858109 / 500000000)) (hi := (617716219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187 / 640) = 1/(640 / 1187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (308858109 / 500000000) (617716219 / 1000000000) (Real.log (1187 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1187 / 640) = -Real.log (640 / 1187) := by
    rw [show ((1187 / 640) : ℝ) = ((640 / 1187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (964434341 / 500000000) ≤ -Real.log (93 / 640) ∧
    -Real.log (93 / 640) ≤ (385773737 / 200000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 93) = 1/(93 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-385773737 / 200000000) (-964434341 / 500000000) (Real.log (93 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (122575461 / 250000000) ≤ -Real.log (1000000 / 1632809) ∧
    -Real.log (1000000 / 1632809) ≤ (98060369 / 200000000) := by
  have h := checkLog_sound (w := (632809 / 2632809)) (n := 12)
    (lo := (122575461 / 250000000)) (hi := (98060369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1632809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1632809 / 1000000) = 1/(1000000 / 1632809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (122575461 / 250000000) (98060369 / 200000000) (Real.log (1632809 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1632809 / 1000000) = -Real.log (1000000 / 1632809) := by
    rw [show ((1632809 / 1000000) : ℝ) = ((1000000 / 1632809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1001873129 / 1000000000) ≤ -Real.log (367191 / 1000000) ∧
    -Real.log (367191 / 1000000) ≤ (1001873131 / 1000000000) := by
  have h := checkLog_sound (w := (132809 / 867191)) (n := 12)
    (lo := (308725949 / 1000000000)) (hi := (6174519 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 367191) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 367191) = 1/(367191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1001873131 / 1000000000) (-1001873129 / 1000000000) (Real.log (367191 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (491527813 / 1000000000) ≤ -Real.log (250000 / 408703) ∧
    -Real.log (250000 / 408703) ≤ (245763907 / 500000000) := by
  have h := checkLog_sound (w := (158703 / 658703)) (n := 12)
    (lo := (491527813 / 1000000000)) (hi := (245763907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((408703 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(408703 / 250000) = 1/(250000 / 408703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (491527813 / 1000000000) (245763907 / 500000000) (Real.log (408703 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (408703 / 250000) = -Real.log (250000 / 408703) := by
    rw [show ((408703 / 250000) : ℝ) = ((250000 / 408703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (251835747 / 250000000) ≤ -Real.log (91297 / 250000) ∧
    -Real.log (91297 / 250000) ≤ (100734299 / 100000000) := by
  have h := checkLog_sound (w := (33703 / 216297)) (n := 12)
    (lo := (9818619 / 31250000)) (hi := (314195809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 91297) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 91297) = 1/(91297 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-100734299 / 100000000) (-251835747 / 250000000) (Real.log (91297 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (20362509 / 50000000) ≤ -Real.log (25000 / 37567) ∧
    -Real.log (25000 / 37567) ≤ (407250181 / 1000000000) := by
  have h := checkLog_sound (w := (12567 / 62567)) (n := 12)
    (lo := (20362509 / 50000000)) (hi := (407250181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37567 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37567 / 25000) = 1/(25000 / 37567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (20362509 / 50000000) (407250181 / 1000000000) (Real.log (37567 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (37567 / 25000) = -Real.log (25000 / 37567) := by
    rw [show ((37567 / 25000) : ℝ) = ((25000 / 37567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (174630399 / 250000000) ≤ -Real.log (12433 / 25000) ∧
    -Real.log (12433 / 25000) ≤ (349260799 / 500000000) := by
  have h := checkLog_sound (w := (67 / 24933)) (n := 12)
    (lo := (335901 / 62500000)) (hi := (5374417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 12433) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12500 / 12433) = 1/(12433 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-349260799 / 500000000) (-174630399 / 250000000) (Real.log (12433 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (204283147 / 500000000) ≤ -Real.log (1000000 / 1504659) ∧
    -Real.log (1000000 / 1504659) ≤ (81713259 / 200000000) := by
  have h := checkLog_sound (w := (504659 / 2504659)) (n := 12)
    (lo := (204283147 / 500000000)) (hi := (81713259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1504659 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1504659 / 1000000) = 1/(1000000 / 1504659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (204283147 / 500000000) (81713259 / 200000000) (Real.log (1504659 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1504659 / 1000000) = -Real.log (1000000 / 1504659) := by
    rw [show ((1504659 / 1000000) : ℝ) = ((1000000 / 1504659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (10976701 / 15625000) ≤ -Real.log (495341 / 1000000) ∧
    -Real.log (495341 / 1000000) ≤ (351254433 / 500000000) := by
  have h := checkLog_sound (w := (4659 / 995341)) (n := 12)
    (lo := (2340421 / 250000000)) (hi := (1872337 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 495341) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 495341) = 1/(495341 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-351254433 / 500000000) (-10976701 / 15625000) (Real.log (495341 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1492174973 / 1000000000) ≤ -Real.log (500000000000 / 2223378296309) ∧
    -Real.log (500000000000 / 2223378296309) ≤ (11657617 / 7812500) := by
  have h := checkLog_sound (w := (223378296309 / 4223378296309)) (n := 12)
    (lo := (105880613 / 1000000000)) (hi := (52940307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2223378296309 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2223378296309 / 2000000000000) = 1/(500000000000 / 2223378296309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1492174973 / 1000000000) (11657617 / 7812500) (Real.log (2223378296309 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2223378296309 / 500000000000) = -Real.log (500000000000 / 2223378296309) := by
    rw [show ((2223378296309 / 500000000000) : ℝ) = ((500000000000 / 2223378296309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1498870801 / 1000000000) ≤ -Real.log (62500000000 / 279789450913) ∧
    -Real.log (62500000000 / 279789450913) ≤ (374717701 / 250000000) := by
  have h := checkLog_sound (w := (29789450913 / 529789450913)) (n := 12)
    (lo := (112576441 / 1000000000)) (hi := (56288221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279789450913 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(279789450913 / 250000000000) = 1/(62500000000 / 279789450913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1498870801 / 1000000000) (374717701 / 250000000) (Real.log (279789450913 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (279789450913 / 62500000000) = -Real.log (62500000000 / 279789450913) := by
    rw [show ((279789450913 / 62500000000) : ℝ) = ((62500000000 / 279789450913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4319421 / 3906250) ≤ -Real.log (12500000000 / 37769444221) ∧
    -Real.log (12500000000 / 37769444221) ≤ (552885889 / 500000000) := by
  have h := checkLog_sound (w := (12769444221 / 62769444221)) (n := 12)
    (lo := (103156149 / 250000000)) (hi := (412624597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37769444221 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(37769444221 / 25000000000) = 1/(12500000000 / 37769444221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4319421 / 3906250) (552885889 / 500000000) (Real.log (37769444221 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (37769444221 / 12500000000) = -Real.log (12500000000 / 37769444221) := by
    rw [show ((37769444221 / 12500000000) : ℝ) = ((12500000000 / 37769444221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (555537579 / 500000000) ≤ -Real.log (500000000000 / 1518811283541) ∧
    -Real.log (500000000000 / 1518811283541) ≤ (27776879 / 25000000) := by
  have h := checkLog_sound (w := (518811283541 / 2518811283541)) (n := 12)
    (lo := (208963989 / 500000000)) (hi := (417927979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1518811283541 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1518811283541 / 1000000000000) = 1/(500000000000 / 1518811283541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (555537579 / 500000000) (27776879 / 25000000) (Real.log (1518811283541 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1518811283541 / 500000000000) = -Real.log (500000000000 / 1518811283541) := by
    rw [show ((1518811283541 / 500000000000) : ℝ) = ((500000000000 / 1518811283541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0072
