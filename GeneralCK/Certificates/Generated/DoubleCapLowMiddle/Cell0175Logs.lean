import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0175
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

theorem reflection_log_1_neg : (31696391 / 50000000) ≤ -Real.log (200 / 377) ∧
    -Real.log (200 / 377) ≤ (633927821 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 577)) (n := 12)
    (lo := (31696391 / 50000000)) (hi := (633927821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((377 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(377 / 200) = 1/(200 / 377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (31696391 / 50000000) (633927821 / 1000000000) (Real.log (377 / 200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (377 / 200) = -Real.log (200 / 377) := by
    rw [show ((377 / 200) : ℝ) = ((200 / 377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (540705787 / 250000000) ≤ -Real.log (23 / 200) ∧
    -Real.log (23 / 200) ≤ (135176447 / 62500000) := by
  have h := checkLog_sound (w := (1 / 24)) (n := 12)
    (lo := (10422701 / 125000000)) (hi := (83381609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 23) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25 / 23) = 1/(23 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-135176447 / 62500000) (-540705787 / 250000000) (Real.log (23 / 200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (126470329 / 200000000) ≤ -Real.log (1280 / 2409) ∧
    -Real.log (1280 / 2409) ≤ (316175823 / 500000000) := by
  have h := checkLog_sound (w := (1129 / 3689)) (n := 12)
    (lo := (126470329 / 200000000)) (hi := (316175823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2409 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2409 / 1280) = 1/(1280 / 2409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (126470329 / 200000000) (316175823 / 500000000) (Real.log (2409 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2409 / 1280) = -Real.log (1280 / 2409) := by
    rw [show ((2409 / 1280) : ℝ) = ((1280 / 2409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1068667759 / 500000000) ≤ -Real.log (151 / 1280) ∧
    -Real.log (151 / 1280) ≤ (1068667761 / 500000000) := by
  have h := checkLog_sound (w := (9 / 311)) (n := 12)
    (lo := (28946989 / 500000000)) (hi := (57893979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 151) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 151) = 1/(151 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1068667761 / 500000000) (-1068667759 / 500000000) (Real.log (151 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (285489773 / 500000000) ≤ -Real.log (100 / 177) ∧
    -Real.log (100 / 177) ≤ (570979547 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 277)) (n := 12)
    (lo := (285489773 / 500000000)) (hi := (570979547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177 / 100) = 1/(100 / 177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (285489773 / 500000000) (570979547 / 1000000000) (Real.log (177 / 100)) := by
  have h := reflection_log_5_neg
  have he : Real.log (177 / 100) = -Real.log (100 / 177) := by
    rw [show ((177 / 100) : ℝ) = ((100 / 177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (22963687 / 15625000) ≤ -Real.log (23 / 100) ∧
    -Real.log (23 / 100) ≤ (1469675971 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 24)) (n := 12)
    (lo := (10422701 / 125000000)) (hi := (83381609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 23) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25 / 23) = 1/(23 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1469675971 / 1000000000) (-22963687 / 15625000) (Real.log (23 / 100)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (567619387 / 1000000000) ≤ -Real.log (640 / 1129) ∧
    -Real.log (640 / 1129) ≤ (141904847 / 250000000) := by
  have h := checkLog_sound (w := (489 / 1769)) (n := 12)
    (lo := (567619387 / 1000000000)) (hi := (141904847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129 / 640) = 1/(640 / 1129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (567619387 / 1000000000) (141904847 / 250000000) (Real.log (1129 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1129 / 640) = -Real.log (640 / 1129) := by
    rw [show ((1129 / 640) : ℝ) = ((640 / 1129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (722094169 / 500000000) ≤ -Real.log (151 / 640) ∧
    -Real.log (151 / 640) ≤ (1444188341 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 311)) (n := 12)
    (lo := (28946989 / 500000000)) (hi := (57893979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 151) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 151) = 1/(151 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1444188341 / 1000000000) (-722094169 / 500000000) (Real.log (151 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (323908823 / 500000000) ≤ -Real.log (200000 / 382273) ∧
    -Real.log (200000 / 382273) ≤ (647817647 / 1000000000) := by
  have h := checkLog_sound (w := (182273 / 582273)) (n := 12)
    (lo := (323908823 / 500000000)) (hi := (647817647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382273 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(382273 / 200000) = 1/(200000 / 382273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (323908823 / 500000000) (647817647 / 1000000000) (Real.log (382273 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (382273 / 200000) = -Real.log (200000 / 382273) := by
    rw [show ((382273 / 200000) : ℝ) = ((200000 / 382273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2423228463 / 1000000000) ≤ -Real.log (17727 / 200000) ∧
    -Real.log (17727 / 200000) ≤ (2423228467 / 1000000000) := by
  have h := checkLog_sound (w := (7273 / 42727)) (n := 12)
    (lo := (343786923 / 1000000000)) (hi := (85946731 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17727) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 17727) = 1/(17727 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2423228467 / 1000000000) (-2423228463 / 1000000000) (Real.log (17727 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (648838907 / 1000000000) ≤ -Real.log (500000 / 956659) ∧
    -Real.log (500000 / 956659) ≤ (162209727 / 250000000) := by
  have h := checkLog_sound (w := (456659 / 1456659)) (n := 12)
    (lo := (648838907 / 1000000000)) (hi := (162209727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((956659 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(956659 / 500000) = 1/(500000 / 956659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (648838907 / 1000000000) (162209727 / 250000000) (Real.log (956659 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (956659 / 500000) = -Real.log (500000 / 956659) := by
    rw [show ((956659 / 500000) : ℝ) = ((500000 / 956659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2445509027 / 1000000000) ≤ -Real.log (43341 / 500000) ∧
    -Real.log (43341 / 500000) ≤ (2445509031 / 1000000000) := by
  have h := checkLog_sound (w := (19159 / 105841)) (n := 12)
    (lo := (366067487 / 1000000000)) (hi := (11439609 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43341) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 43341) = 1/(43341 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2445509031 / 1000000000) (-2445509027 / 1000000000) (Real.log (43341 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (645992677 / 1000000000) ≤ -Real.log (25000 / 47697) ∧
    -Real.log (25000 / 47697) ≤ (322996339 / 500000000) := by
  have h := checkLog_sound (w := (22697 / 72697)) (n := 12)
    (lo := (645992677 / 1000000000)) (hi := (322996339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47697 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47697 / 25000) = 1/(25000 / 47697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (645992677 / 1000000000) (322996339 / 500000000) (Real.log (47697 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (47697 / 25000) = -Real.log (25000 / 47697) := by
    rw [show ((47697 / 25000) : ℝ) = ((25000 / 47697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1192331601 / 500000000) ≤ -Real.log (2303 / 25000) ∧
    -Real.log (2303 / 25000) ≤ (1192331603 / 500000000) := by
  have h := checkLog_sound (w := (411 / 2714)) (n := 12)
    (lo := (152610831 / 500000000)) (hi := (305221663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2303) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3125 / 2303) = 1/(2303 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1192331603 / 500000000) (-1192331601 / 500000000) (Real.log (2303 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (323560783 / 500000000) ≤ -Real.log (200000 / 382007) ∧
    -Real.log (200000 / 382007) ≤ (647121567 / 1000000000) := by
  have h := checkLog_sound (w := (182007 / 582007)) (n := 12)
    (lo := (323560783 / 500000000)) (hi := (647121567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382007 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(382007 / 200000) = 1/(200000 / 382007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (323560783 / 500000000) (647121567 / 1000000000) (Real.log (382007 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (382007 / 200000) = -Real.log (200000 / 382007) := by
    rw [show ((382007 / 200000) : ℝ) = ((200000 / 382007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2408334571 / 1000000000) ≤ -Real.log (17993 / 200000) ∧
    -Real.log (17993 / 200000) ≤ (96333383 / 40000000) := by
  have h := checkLog_sound (w := (7007 / 42993)) (n := 12)
    (lo := (328893031 / 1000000000)) (hi := (41111629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17993) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 17993) = 1/(17993 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-96333383 / 40000000) (-2408334571 / 1000000000) (Real.log (17993 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3071046109 / 1000000000) ≤ -Real.log (500000000000 / 10782224854741) ∧
    -Real.log (500000000000 / 10782224854741) ≤ (1535523057 / 500000000) := by
  have h := checkLog_sound (w := (2782224854741 / 18782224854741)) (n := 12)
    (lo := (298457389 / 1000000000)) (hi := (29845739 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10782224854741 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10782224854741 / 8000000000000) = 1/(500000000000 / 10782224854741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3071046109 / 1000000000) (1535523057 / 500000000) (Real.log (10782224854741 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10782224854741 / 500000000000) = -Real.log (500000000000 / 10782224854741) := by
    rw [show ((10782224854741 / 500000000000) : ℝ) = ((500000000000 / 10782224854741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1547173967 / 500000000) ≤ -Real.log (250000000000 / 5518210239727) ∧
    -Real.log (250000000000 / 5518210239727) ≤ (3094347939 / 1000000000) := by
  have h := checkLog_sound (w := (1518210239727 / 9518210239727)) (n := 12)
    (lo := (160879607 / 500000000)) (hi := (64351843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5518210239727 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(5518210239727 / 4000000000000) = 1/(250000000000 / 5518210239727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1547173967 / 500000000) (3094347939 / 1000000000) (Real.log (5518210239727 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5518210239727 / 250000000000) = -Real.log (250000000000 / 5518210239727) := by
    rw [show ((5518210239727 / 250000000000) : ℝ) = ((250000000000 / 5518210239727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3030655879 / 1000000000) ≤ -Real.log (62500000000 / 1294425749023) ∧
    -Real.log (62500000000 / 1294425749023) ≤ (757663971 / 250000000) := by
  have h := checkLog_sound (w := (294425749023 / 2294425749023)) (n := 12)
    (lo := (258067159 / 1000000000)) (hi := (6451679 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1294425749023 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1294425749023 / 1000000000000) = 1/(62500000000 / 1294425749023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3030655879 / 1000000000) (757663971 / 250000000) (Real.log (1294425749023 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1294425749023 / 62500000000) = -Real.log (62500000000 / 1294425749023) := by
    rw [show ((1294425749023 / 62500000000) : ℝ) = ((62500000000 / 1294425749023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3055456137 / 1000000000) ≤ -Real.log (125000000000 / 2653858444951) ∧
    -Real.log (125000000000 / 2653858444951) ≤ (1527728071 / 500000000) := by
  have h := checkLog_sound (w := (653858444951 / 4653858444951)) (n := 12)
    (lo := (282867417 / 1000000000)) (hi := (141433709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2653858444951 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2653858444951 / 2000000000000) = 1/(125000000000 / 2653858444951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3055456137 / 1000000000) (1527728071 / 500000000) (Real.log (2653858444951 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2653858444951 / 125000000000) = -Real.log (125000000000 / 2653858444951) := by
    rw [show ((2653858444951 / 125000000000) : ℝ) = ((125000000000 / 2653858444951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0175
