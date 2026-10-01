import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0305
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

theorem reflection_log_1_neg : (4455057 / 20000000) ≤ -Real.log (2048 / 2559) ∧
    -Real.log (2048 / 2559) ≤ (222752851 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 4607)) (n := 12)
    (lo := (4455057 / 20000000)) (hi := (222752851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2559 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2559 / 2048) = 1/(2048 / 2559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (4455057 / 20000000) (222752851 / 1000000000) (Real.log (2559 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2559 / 2048) = -Real.log (2048 / 2559) := by
    rw [show ((2559 / 2048) : ℝ) = ((2048 / 2559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (143515621 / 500000000) ≤ -Real.log (1537 / 2048) ∧
    -Real.log (1537 / 2048) ≤ (287031243 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 3585)) (n := 12)
    (lo := (143515621 / 500000000)) (hi := (287031243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1537) = 1/(1537 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-287031243 / 1000000000) (-143515621 / 500000000) (Real.log (1537 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (44503671 / 200000000) ≤ -Real.log (1280 / 1599) ∧
    -Real.log (1280 / 1599) ≤ (55629589 / 250000000) := by
  have h := checkLog_sound (w := (319 / 2879)) (n := 12)
    (lo := (44503671 / 200000000)) (hi := (55629589 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1599 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1599 / 1280) = 1/(1280 / 1599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (44503671 / 200000000) (55629589 / 250000000) (Real.log (1599 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1599 / 1280) = -Real.log (1280 / 1599) := by
    rw [show ((1599 / 1280) : ℝ) = ((1280 / 1599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (286640947 / 1000000000) ≤ -Real.log (961 / 1280) ∧
    -Real.log (961 / 1280) ≤ (71660237 / 250000000) := by
  have h := checkLog_sound (w := (319 / 2241)) (n := 12)
    (lo := (286640947 / 1000000000)) (hi := (71660237 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 961) = 1/(961 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-71660237 / 250000000) (-286640947 / 1000000000) (Real.log (961 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (202406927 / 500000000) ≤ -Real.log (1024 / 1535) ∧
    -Real.log (1024 / 1535) ≤ (80962771 / 200000000) := by
  have h := checkLog_sound (w := (511 / 2559)) (n := 12)
    (lo := (202406927 / 500000000)) (hi := (80962771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1535 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1535 / 1024) = 1/(1024 / 1535) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (202406927 / 500000000) (80962771 / 200000000) (Real.log (1535 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1535 / 1024) = -Real.log (1024 / 1535) := by
    rw [show ((1535 / 1024) : ℝ) = ((1024 / 1535) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (17279899 / 25000000) ≤ -Real.log (513 / 1024) ∧
    -Real.log (513 / 1024) ≤ (691195961 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 1537)) (n := 12)
    (lo := (17279899 / 25000000)) (hi := (691195961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 513) = 1/(513 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-691195961 / 1000000000) (-17279899 / 25000000) (Real.log (513 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (202211449 / 500000000) ≤ -Real.log (640 / 959) ∧
    -Real.log (640 / 959) ≤ (404422899 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 1599)) (n := 12)
    (lo := (202211449 / 500000000)) (hi := (404422899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959 / 640) = 1/(640 / 959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (202211449 / 500000000) (404422899 / 1000000000) (Real.log (959 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (959 / 640) = -Real.log (640 / 959) := by
    rw [show ((959 / 640) : ℝ) = ((640 / 959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (690027053 / 1000000000) ≤ -Real.log (321 / 640) ∧
    -Real.log (321 / 640) ≤ (345013527 / 500000000) := by
  have h := checkLog_sound (w := (319 / 961)) (n := 12)
    (lo := (690027053 / 1000000000)) (hi := (345013527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 321) = 1/(321 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-345013527 / 500000000) (-690027053 / 1000000000) (Real.log (321 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (152465721 / 500000000) ≤ -Real.log (250000 / 339133) ∧
    -Real.log (250000 / 339133) ≤ (304931443 / 1000000000) := by
  have h := checkLog_sound (w := (89133 / 589133)) (n := 12)
    (lo := (152465721 / 500000000)) (hi := (304931443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339133 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339133 / 250000) = 1/(250000 / 339133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (152465721 / 500000000) (304931443 / 1000000000) (Real.log (339133 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (339133 / 250000) = -Real.log (250000 / 339133) := by
    rw [show ((339133 / 250000) : ℝ) = ((250000 / 339133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (440882981 / 1000000000) ≤ -Real.log (160867 / 250000) ∧
    -Real.log (160867 / 250000) ≤ (220441491 / 500000000) := by
  have h := checkLog_sound (w := (89133 / 410867)) (n := 12)
    (lo := (440882981 / 1000000000)) (hi := (220441491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 160867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 160867) = 1/(160867 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-220441491 / 500000000) (-440882981 / 1000000000) (Real.log (160867 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (152624557 / 500000000) ≤ -Real.log (1000000 / 1356963) ∧
    -Real.log (1000000 / 1356963) ≤ (61049823 / 200000000) := by
  have h := checkLog_sound (w := (356963 / 2356963)) (n := 12)
    (lo := (152624557 / 500000000)) (hi := (61049823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1356963 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1356963 / 1000000) = 1/(1000000 / 1356963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (152624557 / 500000000) (61049823 / 200000000) (Real.log (1356963 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1356963 / 1000000) = -Real.log (1000000 / 1356963) := by
    rw [show ((1356963 / 1000000) : ℝ) = ((1000000 / 1356963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (441553013 / 1000000000) ≤ -Real.log (643037 / 1000000) ∧
    -Real.log (643037 / 1000000) ≤ (220776507 / 500000000) := by
  have h := checkLog_sound (w := (356963 / 1643037)) (n := 12)
    (lo := (441553013 / 1000000000)) (hi := (220776507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 643037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 643037) = 1/(643037 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-220776507 / 500000000) (-441553013 / 1000000000) (Real.log (643037 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23213897 / 100000000) ≤ -Real.log (200000 / 252259) ∧
    -Real.log (200000 / 252259) ≤ (232138971 / 1000000000) := by
  have h := checkLog_sound (w := (52259 / 452259)) (n := 12)
    (lo := (23213897 / 100000000)) (hi := (232138971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252259 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(252259 / 200000) = 1/(200000 / 252259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23213897 / 100000000) (232138971 / 1000000000) (Real.log (252259 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (252259 / 200000) = -Real.log (200000 / 252259) := by
    rw [show ((252259 / 200000) : ℝ) = ((200000 / 252259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2422853 / 8000000) ≤ -Real.log (147741 / 200000) ∧
    -Real.log (147741 / 200000) ≤ (151428313 / 500000000) := by
  have h := checkLog_sound (w := (52259 / 347741)) (n := 12)
    (lo := (2422853 / 8000000)) (hi := (151428313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 147741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 147741) = 1/(147741 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-151428313 / 500000000) (-2422853 / 8000000) (Real.log (147741 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (116203853 / 500000000) ≤ -Real.log (500000 / 630817) ∧
    -Real.log (500000 / 630817) ≤ (232407707 / 1000000000) := by
  have h := checkLog_sound (w := (130817 / 1130817)) (n := 12)
    (lo := (116203853 / 500000000)) (hi := (232407707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630817 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630817 / 500000) = 1/(500000 / 630817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (116203853 / 500000000) (232407707 / 1000000000) (Real.log (630817 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (630817 / 500000) = -Real.log (500000 / 630817) := by
    rw [show ((630817 / 500000) : ℝ) = ((500000 / 630817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (151657821 / 500000000) ≤ -Real.log (369183 / 500000) ∧
    -Real.log (369183 / 500000) ≤ (303315643 / 1000000000) := by
  have h := checkLog_sound (w := (130817 / 869183)) (n := 12)
    (lo := (151657821 / 500000000)) (hi := (303315643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 369183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 369183) = 1/(369183 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-303315643 / 1000000000) (-151657821 / 500000000) (Real.log (369183 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (745814423 / 1000000000) ≤ -Real.log (500000000000 / 1054078835311) ∧
    -Real.log (500000000000 / 1054078835311) ≤ (29832577 / 40000000) := by
  have h := checkLog_sound (w := (54078835311 / 2054078835311)) (n := 12)
    (lo := (52667243 / 1000000000)) (hi := (13166811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1054078835311 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1054078835311 / 1000000000000) = 1/(500000000000 / 1054078835311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (745814423 / 1000000000) (29832577 / 40000000) (Real.log (1054078835311 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1054078835311 / 500000000000) = -Real.log (500000000000 / 1054078835311) := by
    rw [show ((1054078835311 / 500000000000) : ℝ) = ((500000000000 / 1054078835311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (746802127 / 1000000000) ≤ -Real.log (31250000000 / 65945029213) ∧
    -Real.log (31250000000 / 65945029213) ≤ (746802129 / 1000000000) := by
  have h := checkLog_sound (w := (3445029213 / 128445029213)) (n := 12)
    (lo := (53654947 / 1000000000)) (hi := (13413737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65945029213 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(65945029213 / 62500000000) = 1/(31250000000 / 65945029213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (746802127 / 1000000000) (746802129 / 1000000000) (Real.log (65945029213 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (65945029213 / 31250000000) = -Real.log (31250000000 / 65945029213) := by
    rw [show ((65945029213 / 31250000000) : ℝ) = ((31250000000 / 65945029213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (133748899 / 250000000) ≤ -Real.log (488281250 / 833711291) ∧
    -Real.log (488281250 / 833711291) ≤ (534995597 / 1000000000) := by
  have h := checkLog_sound (w := (345430041 / 1321992541)) (n := 12)
    (lo := (133748899 / 250000000)) (hi := (534995597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((833711291 / 488281250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(833711291 / 488281250) = 1/(488281250 / 833711291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (133748899 / 250000000) (534995597 / 1000000000) (Real.log (833711291 / 488281250)) := by
  have h := reflection_log_19_neg
  have he : Real.log (833711291 / 488281250) = -Real.log (488281250 / 833711291) := by
    rw [show ((833711291 / 488281250) : ℝ) = ((488281250 / 833711291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (133930837 / 250000000) ≤ -Real.log (62500000000 / 106792735581) ∧
    -Real.log (62500000000 / 106792735581) ≤ (535723349 / 1000000000) := by
  have h := checkLog_sound (w := (44292735581 / 169292735581)) (n := 12)
    (lo := (133930837 / 250000000)) (hi := (535723349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106792735581 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106792735581 / 62500000000) = 1/(62500000000 / 106792735581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (133930837 / 250000000) (535723349 / 1000000000) (Real.log (106792735581 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (106792735581 / 62500000000) = -Real.log (62500000000 / 106792735581) := by
    rw [show ((106792735581 / 62500000000) : ℝ) = ((62500000000 / 106792735581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0305
