import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11520_neg : (278434781 / 500000000) ≤ -Real.log (573 / 1000) ∧
    -Real.log (573 / 1000) ≤ (556869563 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 1573)) (n := 12)
    (lo := (278434781 / 500000000)) (hi := (556869563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 573) = 1/(573 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11520 : Bounds (-556869563 / 1000000000) (-278434781 / 500000000) (Real.log (573 / 1000)) := by
  have h := reflection_log_11520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11521_neg : (106727 / 250000000) ≤ -Real.log (1000000 / 1000427) ∧
    -Real.log (1000000 / 1000427) ≤ (426909 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 2000427)) (n := 12)
    (lo := (106727 / 250000000)) (hi := (426909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000427 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000427 / 1000000) = 1/(1000000 / 1000427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11521 : Bounds (106727 / 250000000) (426909 / 1000000000) (Real.log (1000427 / 1000000)) := by
  have h := reflection_log_11521_neg
  have he : Real.log (1000427 / 1000000) = -Real.log (1000000 / 1000427) := by
    rw [show ((1000427 / 1000000) : ℝ) = ((1000000 / 1000427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11522_neg : (427091 / 1000000000) ≤ -Real.log (999573 / 1000000) ∧
    -Real.log (999573 / 1000000) ≤ (106773 / 250000000) := by
  have h := checkLog_sound (w := (427 / 1999573)) (n := 12)
    (lo := (427091 / 1000000000)) (hi := (106773 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999573) = 1/(999573 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11522 : Bounds (-106773 / 250000000) (-427091 / 1000000000) (Real.log (999573 / 1000000)) := by
  have h := reflection_log_11522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11523_neg : (99493867 / 500000000) ≤ -Real.log (1000000 / 1220167) ∧
    -Real.log (1000000 / 1220167) ≤ (39797547 / 200000000) := by
  have h := checkLog_sound (w := (220167 / 2220167)) (n := 12)
    (lo := (99493867 / 500000000)) (hi := (39797547 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1220167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1220167 / 1000000) = 1/(1000000 / 1220167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11523 : Bounds (99493867 / 500000000) (39797547 / 200000000) (Real.log (1220167 / 1000000)) := by
  have h := reflection_log_11523_neg
  have he : Real.log (1220167 / 1000000) = -Real.log (1000000 / 1220167) := by
    rw [show ((1220167 / 1000000) : ℝ) = ((1000000 / 1220167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11524_neg : (62168871 / 250000000) ≤ -Real.log (779833 / 1000000) ∧
    -Real.log (779833 / 1000000) ≤ (49735097 / 200000000) := by
  have h := checkLog_sound (w := (220167 / 1779833)) (n := 12)
    (lo := (62168871 / 250000000)) (hi := (49735097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 779833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 779833) = 1/(779833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11524 : Bounds (-49735097 / 200000000) (-62168871 / 250000000) (Real.log (779833 / 1000000)) := by
  have h := reflection_log_11524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11525_neg : (49944779 / 250000000) ≤ -Real.log (1000000 / 1221133) ∧
    -Real.log (1000000 / 1221133) ≤ (199779117 / 1000000000) := by
  have h := checkLog_sound (w := (221133 / 2221133)) (n := 12)
    (lo := (49944779 / 250000000)) (hi := (199779117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221133 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1221133 / 1000000) = 1/(1000000 / 1221133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11525 : Bounds (49944779 / 250000000) (199779117 / 1000000000) (Real.log (1221133 / 1000000)) := by
  have h := reflection_log_11525_neg
  have he : Real.log (1221133 / 1000000) = -Real.log (1000000 / 1221133) := by
    rw [show ((1221133 / 1000000) : ℝ) = ((1000000 / 1221133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11526_neg : (249914979 / 1000000000) ≤ -Real.log (778867 / 1000000) ∧
    -Real.log (778867 / 1000000) ≤ (12495749 / 50000000) := by
  have h := checkLog_sound (w := (221133 / 1778867)) (n := 12)
    (lo := (249914979 / 1000000000)) (hi := (12495749 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 778867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 778867) = 1/(778867 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11526 : Bounds (-12495749 / 50000000) (-249914979 / 1000000000) (Real.log (778867 / 1000000)) := by
  have h := reflection_log_11526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11527_neg : (50135863 / 1000000000) ≤ -Real.log (951100196311 / 1000000000000) ∧
    -Real.log (951100196311 / 1000000000000) ≤ (6266983 / 125000000) := by
  have h := checkLog_sound (w := (48899803689 / 1951100196311)) (n := 12)
    (lo := (50135863 / 1000000000)) (hi := (6266983 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 951100196311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 951100196311) = 1/(951100196311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11527 : Bounds (-6266983 / 125000000) (-50135863 / 1000000000) (Real.log (951100196311 / 1000000000000)) := by
  have h := reflection_log_11527_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11528_neg : (198751 / 4000000) ≤ -Real.log (951526492111 / 1000000000000) ∧
    -Real.log (951526492111 / 1000000000000) ≤ (49687751 / 1000000000) := by
  have h := checkLog_sound (w := (48473507889 / 1951526492111)) (n := 12)
    (lo := (198751 / 4000000)) (hi := (49687751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 951526492111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 951526492111) = 1/(951526492111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11528 : Bounds (-49687751 / 1000000000) (-198751 / 4000000) (Real.log (951526492111 / 1000000000000)) := by
  have h := reflection_log_11528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11529_neg : (447663219 / 1000000000) ≤ -Real.log (500000000000 / 782325831299) ∧
    -Real.log (500000000000 / 782325831299) ≤ (22383161 / 50000000) := by
  have h := checkLog_sound (w := (282325831299 / 1282325831299)) (n := 12)
    (lo := (447663219 / 1000000000)) (hi := (22383161 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782325831299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782325831299 / 500000000000) = 1/(500000000000 / 782325831299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11529 : Bounds (447663219 / 1000000000) (22383161 / 50000000) (Real.log (782325831299 / 500000000000)) := by
  have h := reflection_log_11529_neg
  have he : Real.log (782325831299 / 500000000000) = -Real.log (500000000000 / 782325831299) := by
    rw [show ((782325831299 / 500000000000) : ℝ) = ((500000000000 / 782325831299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11530_neg : (89938819 / 200000000) ≤ -Real.log (500000000000 / 783916252711) ∧
    -Real.log (500000000000 / 783916252711) ≤ (28105881 / 62500000) := by
  have h := checkLog_sound (w := (283916252711 / 1283916252711)) (n := 12)
    (lo := (89938819 / 200000000)) (hi := (28105881 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((783916252711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(783916252711 / 500000000000) = 1/(500000000000 / 783916252711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11530 : Bounds (89938819 / 200000000) (28105881 / 62500000) (Real.log (783916252711 / 500000000000)) := by
  have h := reflection_log_11530_neg
  have he : Real.log (783916252711 / 500000000000) = -Real.log (500000000000 / 783916252711) := by
    rw [show ((783916252711 / 500000000000) : ℝ) = ((500000000000 / 783916252711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11531_neg : (227499801 / 250000000) ≤ -Real.log (100000000000 / 248432055749) ∧
    -Real.log (100000000000 / 248432055749) ≤ (454999603 / 500000000) := by
  have h := checkLog_sound (w := (48432055749 / 448432055749)) (n := 12)
    (lo := (27106503 / 125000000)) (hi := (8674081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248432055749 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(248432055749 / 200000000000) = 1/(100000000000 / 248432055749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11531 : Bounds (227499801 / 250000000) (454999603 / 500000000) (Real.log (248432055749 / 100000000000)) := by
  have h := reflection_log_11531_neg
  have he : Real.log (248432055749 / 100000000000) = -Real.log (100000000000 / 248432055749) := by
    rw [show ((248432055749 / 100000000000) : ℝ) = ((100000000000 / 248432055749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11532_neg : (9124439 / 10000000) ≤ -Real.log (500000000000 / 1245200698081) ∧
    -Real.log (500000000000 / 1245200698081) ≤ (456221951 / 500000000) := by
  have h := checkLog_sound (w := (245200698081 / 2245200698081)) (n := 12)
    (lo := (2741209 / 12500000)) (hi := (219296721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245200698081 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1245200698081 / 1000000000000) = 1/(500000000000 / 1245200698081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11532 : Bounds (9124439 / 10000000) (456221951 / 500000000) (Real.log (1245200698081 / 500000000000)) := by
  have h := reflection_log_11532_neg
  have he : Real.log (1245200698081 / 500000000000) = -Real.log (500000000000 / 1245200698081) := by
    rw [show ((1245200698081 / 500000000000) : ℝ) = ((500000000000 / 1245200698081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11533_neg : (356274863 / 1000000000) ≤ -Real.log (250 / 357) ∧
    -Real.log (250 / 357) ≤ (22267179 / 62500000) := by
  have h := checkLog_sound (w := (107 / 607)) (n := 12)
    (lo := (356274863 / 1000000000)) (hi := (22267179 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357 / 250) = 1/(250 / 357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11533 : Bounds (356274863 / 1000000000) (22267179 / 62500000) (Real.log (357 / 250)) := by
  have h := reflection_log_11533_neg
  have he : Real.log (357 / 250) = -Real.log (250 / 357) := by
    rw [show ((357 / 250) : ℝ) = ((250 / 357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11534_neg : (558616287 / 1000000000) ≤ -Real.log (143 / 250) ∧
    -Real.log (143 / 250) ≤ (17456759 / 31250000) := by
  have h := checkLog_sound (w := (107 / 393)) (n := 12)
    (lo := (558616287 / 1000000000)) (hi := (17456759 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 143) = 1/(143 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11534 : Bounds (-17456759 / 31250000) (-558616287 / 1000000000) (Real.log (143 / 250)) := by
  have h := reflection_log_11534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11535_neg : (106977 / 250000000) ≤ -Real.log (250000 / 250107) ∧
    -Real.log (250000 / 250107) ≤ (427909 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 500107)) (n := 12)
    (lo := (106977 / 250000000)) (hi := (427909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250107 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250107 / 250000) = 1/(250000 / 250107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11535 : Bounds (106977 / 250000000) (427909 / 1000000000) (Real.log (250107 / 250000)) := by
  have h := reflection_log_11535_neg
  have he : Real.log (250107 / 250000) = -Real.log (250000 / 250107) := by
    rw [show ((250107 / 250000) : ℝ) = ((250000 / 250107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11536_neg : (428091 / 1000000000) ≤ -Real.log (249893 / 250000) ∧
    -Real.log (249893 / 250000) ≤ (107023 / 250000000) := by
  have h := checkLog_sound (w := (107 / 499893)) (n := 12)
    (lo := (428091 / 1000000000)) (hi := (107023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249893) = 1/(249893 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11536 : Bounds (-107023 / 250000000) (-428091 / 1000000000) (Real.log (249893 / 250000)) := by
  have h := reflection_log_11536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11537_neg : (12465053 / 62500000) ≤ -Real.log (12500 / 15259) ∧
    -Real.log (12500 / 15259) ≤ (199440849 / 1000000000) := by
  have h := checkLog_sound (w := (2759 / 27759)) (n := 12)
    (lo := (12465053 / 62500000)) (hi := (199440849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15259 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15259 / 12500) = 1/(12500 / 15259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11537 : Bounds (12465053 / 62500000) (199440849 / 1000000000) (Real.log (15259 / 12500)) := by
  have h := reflection_log_11537_neg
  have he : Real.log (15259 / 12500) = -Real.log (12500 / 15259) := by
    rw [show ((15259 / 12500) : ℝ) = ((12500 / 15259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11538_neg : (124692431 / 500000000) ≤ -Real.log (9741 / 12500) ∧
    -Real.log (9741 / 12500) ≤ (249384863 / 1000000000) := by
  have h := checkLog_sound (w := (2759 / 22241)) (n := 12)
    (lo := (124692431 / 500000000)) (hi := (249384863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 9741) = 1/(9741 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11538 : Bounds (-249384863 / 1000000000) (-124692431 / 500000000) (Real.log (9741 / 12500)) := by
  have h := reflection_log_11538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11539_neg : (20023269 / 100000000) ≤ -Real.log (1000000 / 1221687) ∧
    -Real.log (1000000 / 1221687) ≤ (200232691 / 1000000000) := by
  have h := checkLog_sound (w := (221687 / 2221687)) (n := 12)
    (lo := (20023269 / 100000000)) (hi := (200232691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221687 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1221687 / 1000000) = 1/(1000000 / 1221687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11539 : Bounds (20023269 / 100000000) (200232691 / 1000000000) (Real.log (1221687 / 1000000)) := by
  have h := reflection_log_11539_neg
  have he : Real.log (1221687 / 1000000) = -Real.log (1000000 / 1221687) := by
    rw [show ((1221687 / 1000000) : ℝ) = ((1000000 / 1221687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11540_neg : (125313261 / 500000000) ≤ -Real.log (778313 / 1000000) ∧
    -Real.log (778313 / 1000000) ≤ (250626523 / 1000000000) := by
  have h := checkLog_sound (w := (221687 / 1778313)) (n := 12)
    (lo := (125313261 / 500000000)) (hi := (250626523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 778313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 778313) = 1/(778313 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11540 : Bounds (-250626523 / 1000000000) (-125313261 / 500000000) (Real.log (778313 / 1000000)) := by
  have h := reflection_log_11540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11541_neg : (50393831 / 1000000000) ≤ -Real.log (950854874031 / 1000000000000) ∧
    -Real.log (950854874031 / 1000000000000) ≤ (6299229 / 125000000) := by
  have h := checkLog_sound (w := (49145125969 / 1950854874031)) (n := 12)
    (lo := (50393831 / 1000000000)) (hi := (6299229 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 950854874031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 950854874031) = 1/(950854874031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11541 : Bounds (-6299229 / 125000000) (-50393831 / 1000000000) (Real.log (950854874031 / 1000000000000)) := by
  have h := reflection_log_11541_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11542_neg : (49944013 / 1000000000) ≤ -Real.log (148637919 / 156250000) ∧
    -Real.log (148637919 / 156250000) ≤ (24972007 / 500000000) := by
  have h := checkLog_sound (w := (7612081 / 304887919)) (n := 12)
    (lo := (49944013 / 1000000000)) (hi := (24972007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 148637919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 148637919) = 1/(148637919 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11542 : Bounds (-24972007 / 500000000) (-49944013 / 1000000000) (Real.log (148637919 / 156250000)) := by
  have h := reflection_log_11542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11543_neg : (448825711 / 1000000000) ≤ -Real.log (500000000000 / 783235807411) ∧
    -Real.log (500000000000 / 783235807411) ≤ (28051607 / 62500000) := by
  have h := checkLog_sound (w := (283235807411 / 1283235807411)) (n := 12)
    (lo := (448825711 / 1000000000)) (hi := (28051607 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((783235807411 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(783235807411 / 500000000000) = 1/(500000000000 / 783235807411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11543 : Bounds (448825711 / 1000000000) (28051607 / 62500000) (Real.log (783235807411 / 500000000000)) := by
  have h := reflection_log_11543_neg
  have he : Real.log (783235807411 / 500000000000) = -Real.log (500000000000 / 783235807411) := by
    rw [show ((783235807411 / 500000000000) : ℝ) = ((500000000000 / 783235807411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11544_neg : (112714803 / 250000000) ≤ -Real.log (62500000000 / 98103767379) ∧
    -Real.log (62500000000 / 98103767379) ≤ (450859213 / 1000000000) := by
  have h := checkLog_sound (w := (35603767379 / 160603767379)) (n := 12)
    (lo := (112714803 / 250000000)) (hi := (450859213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98103767379 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98103767379 / 62500000000) = 1/(62500000000 / 98103767379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11544 : Bounds (112714803 / 250000000) (450859213 / 1000000000) (Real.log (98103767379 / 62500000000)) := by
  have h := reflection_log_11544_neg
  have he : Real.log (98103767379 / 62500000000) = -Real.log (62500000000 / 98103767379) := by
    rw [show ((98103767379 / 62500000000) : ℝ) = ((62500000000 / 98103767379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11545_neg : (9124439 / 10000000) ≤ -Real.log (3125000000 / 7782504363) ∧
    -Real.log (3125000000 / 7782504363) ≤ (456221951 / 500000000) := by
  have h := checkLog_sound (w := (1532504363 / 14032504363)) (n := 12)
    (lo := (2741209 / 12500000)) (hi := (219296721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7782504363 / 6250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(7782504363 / 6250000000) = 1/(3125000000 / 7782504363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11545 : Bounds (9124439 / 10000000) (456221951 / 500000000) (Real.log (7782504363 / 3125000000)) := by
  have h := reflection_log_11545_neg
  have he : Real.log (7782504363 / 3125000000) = -Real.log (3125000000 / 7782504363) := by
    rw [show ((7782504363 / 3125000000) : ℝ) = ((3125000000 / 7782504363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11546_neg : (18297823 / 20000000) ≤ -Real.log (125000000000 / 312062937063) ∧
    -Real.log (125000000000 / 312062937063) ≤ (57180697 / 62500000) := by
  have h := checkLog_sound (w := (62062937063 / 562062937063)) (n := 12)
    (lo := (22174397 / 100000000)) (hi := (221743971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312062937063 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(312062937063 / 250000000000) = 1/(125000000000 / 312062937063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11546 : Bounds (18297823 / 20000000) (57180697 / 62500000) (Real.log (312062937063 / 125000000000)) := by
  have h := reflection_log_11546_neg
  have he : Real.log (312062937063 / 125000000000) = -Real.log (125000000000 / 312062937063) := by
    rw [show ((312062937063 / 125000000000) : ℝ) = ((125000000000 / 312062937063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11547_neg : (178487449 / 500000000) ≤ -Real.log (1000 / 1429) ∧
    -Real.log (1000 / 1429) ≤ (356974899 / 1000000000) := by
  have h := checkLog_sound (w := (429 / 2429)) (n := 12)
    (lo := (178487449 / 500000000)) (hi := (356974899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1429 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1429 / 1000) = 1/(1000 / 1429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11547 : Bounds (178487449 / 500000000) (356974899 / 1000000000) (Real.log (1429 / 1000)) := by
  have h := reflection_log_11547_neg
  have he : Real.log (1429 / 1000) = -Real.log (1000 / 1429) := by
    rw [show ((1429 / 1000) : ℝ) = ((1000 / 1429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11548_neg : (560366069 / 1000000000) ≤ -Real.log (571 / 1000) ∧
    -Real.log (571 / 1000) ≤ (56036607 / 100000000) := by
  have h := checkLog_sound (w := (429 / 1571)) (n := 12)
    (lo := (560366069 / 1000000000)) (hi := (56036607 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 571) = 1/(571 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11548 : Bounds (-56036607 / 100000000) (-560366069 / 1000000000) (Real.log (571 / 1000)) := by
  have h := reflection_log_11548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11549_neg : (107227 / 250000000) ≤ -Real.log (1000000 / 1000429) ∧
    -Real.log (1000000 / 1000429) ≤ (428909 / 1000000000) := by
  have h := checkLog_sound (w := (429 / 2000429)) (n := 12)
    (lo := (107227 / 250000000)) (hi := (428909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000429 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000429 / 1000000) = 1/(1000000 / 1000429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11549 : Bounds (107227 / 250000000) (428909 / 1000000000) (Real.log (1000429 / 1000000)) := by
  have h := reflection_log_11549_neg
  have he : Real.log (1000429 / 1000000) = -Real.log (1000000 / 1000429) := by
    rw [show ((1000429 / 1000000) : ℝ) = ((1000000 / 1000429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11550_neg : (107273 / 250000000) ≤ -Real.log (999571 / 1000000) ∧
    -Real.log (999571 / 1000000) ≤ (429093 / 1000000000) := by
  have h := checkLog_sound (w := (429 / 1999571)) (n := 12)
    (lo := (107273 / 250000000)) (hi := (429093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999571) = 1/(999571 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11550 : Bounds (-429093 / 1000000000) (-107273 / 250000000) (Real.log (999571 / 1000000)) := by
  have h := reflection_log_11550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11551_neg : (12493411 / 62500000) ≤ -Real.log (500000 / 610637) ∧
    -Real.log (500000 / 610637) ≤ (199894577 / 1000000000) := by
  have h := checkLog_sound (w := (110637 / 1110637)) (n := 12)
    (lo := (12493411 / 62500000)) (hi := (199894577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610637 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610637 / 500000) = 1/(500000 / 610637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11551 : Bounds (12493411 / 62500000) (199894577 / 1000000000) (Real.log (610637 / 500000)) := by
  have h := reflection_log_11551_neg
  have he : Real.log (610637 / 500000) = -Real.log (500000 / 610637) := by
    rw [show ((610637 / 500000) : ℝ) = ((500000 / 610637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11552_neg : (250096027 / 1000000000) ≤ -Real.log (389363 / 500000) ∧
    -Real.log (389363 / 500000) ≤ (62524007 / 250000000) := by
  have h := checkLog_sound (w := (110637 / 889363)) (n := 12)
    (lo := (250096027 / 1000000000)) (hi := (62524007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 389363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 389363) = 1/(389363 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11552 : Bounds (-62524007 / 250000000) (-250096027 / 1000000000) (Real.log (389363 / 500000)) := by
  have h := reflection_log_11552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11553_neg : (200686877 / 1000000000) ≤ -Real.log (500000 / 611121) ∧
    -Real.log (500000 / 611121) ≤ (100343439 / 500000000) := by
  have h := checkLog_sound (w := (111121 / 1111121)) (n := 12)
    (lo := (200686877 / 1000000000)) (hi := (100343439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611121 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611121 / 500000) = 1/(500000 / 611121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11553 : Bounds (200686877 / 1000000000) (100343439 / 500000000) (Real.log (611121 / 500000)) := by
  have h := reflection_log_11553_neg
  have he : Real.log (611121 / 500000) = -Real.log (500000 / 611121) := by
    rw [show ((611121 / 500000) : ℝ) = ((500000 / 611121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11554_neg : (251339857 / 1000000000) ≤ -Real.log (388879 / 500000) ∧
    -Real.log (388879 / 500000) ≤ (125669929 / 500000000) := by
  have h := checkLog_sound (w := (111121 / 888879)) (n := 12)
    (lo := (251339857 / 1000000000)) (hi := (125669929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 388879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 388879) = 1/(388879 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11554 : Bounds (-125669929 / 500000000) (-251339857 / 1000000000) (Real.log (388879 / 500000)) := by
  have h := reflection_log_11554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11555_neg : (2532649 / 50000000) ≤ -Real.log (237652123359 / 250000000000) ∧
    -Real.log (237652123359 / 250000000000) ≤ (50652981 / 1000000000) := by
  have h := checkLog_sound (w := (12347876641 / 487652123359)) (n := 12)
    (lo := (2532649 / 50000000)) (hi := (50652981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237652123359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237652123359) = 1/(237652123359 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11555 : Bounds (-50652981 / 1000000000) (-2532649 / 50000000) (Real.log (237652123359 / 250000000000)) := by
  have h := reflection_log_11555_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11556_neg : (50201451 / 1000000000) ≤ -Real.log (237759454231 / 250000000000) ∧
    -Real.log (237759454231 / 250000000000) ≤ (12550363 / 250000000) := by
  have h := checkLog_sound (w := (12240545769 / 487759454231)) (n := 12)
    (lo := (50201451 / 1000000000)) (hi := (12550363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237759454231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237759454231) = 1/(237759454231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11556 : Bounds (-12550363 / 250000000) (-50201451 / 1000000000) (Real.log (237759454231 / 250000000000)) := by
  have h := reflection_log_11556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11557_neg : (112497651 / 250000000) ≤ -Real.log (62500000000 / 98018590621) ∧
    -Real.log (62500000000 / 98018590621) ≤ (89998121 / 200000000) := by
  have h := checkLog_sound (w := (35518590621 / 160518590621)) (n := 12)
    (lo := (112497651 / 250000000)) (hi := (89998121 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98018590621 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98018590621 / 62500000000) = 1/(62500000000 / 98018590621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11557 : Bounds (112497651 / 250000000) (89998121 / 200000000) (Real.log (98018590621 / 62500000000)) := by
  have h := reflection_log_11557_neg
  have he : Real.log (98018590621 / 62500000000) = -Real.log (62500000000 / 98018590621) := by
    rw [show ((98018590621 / 62500000000) : ℝ) = ((62500000000 / 98018590621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11558_neg : (226013367 / 500000000) ≤ -Real.log (62500000000 / 98218372553) ∧
    -Real.log (62500000000 / 98218372553) ≤ (90405347 / 200000000) := by
  have h := checkLog_sound (w := (35718372553 / 160718372553)) (n := 12)
    (lo := (226013367 / 500000000)) (hi := (90405347 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98218372553 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98218372553 / 62500000000) = 1/(62500000000 / 98218372553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11558 : Bounds (226013367 / 500000000) (90405347 / 200000000) (Real.log (98218372553 / 62500000000)) := by
  have h := reflection_log_11558_neg
  have he : Real.log (98218372553 / 62500000000) = -Real.log (62500000000 / 98218372553) := by
    rw [show ((98218372553 / 62500000000) : ℝ) = ((62500000000 / 98218372553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11559_neg : (18297823 / 20000000) ≤ -Real.log (500000000000 / 1248251748251) ∧
    -Real.log (500000000000 / 1248251748251) ≤ (57180697 / 62500000) := by
  have h := checkLog_sound (w := (248251748251 / 2248251748251)) (n := 12)
    (lo := (22174397 / 100000000)) (hi := (221743971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1248251748251 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1248251748251 / 1000000000000) = 1/(500000000000 / 1248251748251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11559 : Bounds (18297823 / 20000000) (57180697 / 62500000) (Real.log (1248251748251 / 500000000000)) := by
  have h := reflection_log_11559_neg
  have he : Real.log (1248251748251 / 500000000000) = -Real.log (500000000000 / 1248251748251) := by
    rw [show ((1248251748251 / 500000000000) : ℝ) = ((500000000000 / 1248251748251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11560_neg : (917340967 / 1000000000) ≤ -Real.log (250000000000 / 625656742557) ∧
    -Real.log (250000000000 / 625656742557) ≤ (917340969 / 1000000000) := by
  have h := checkLog_sound (w := (125656742557 / 1125656742557)) (n := 12)
    (lo := (224193787 / 1000000000)) (hi := (56048447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625656742557 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(625656742557 / 500000000000) = 1/(250000000000 / 625656742557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11560 : Bounds (917340967 / 1000000000) (917340969 / 1000000000) (Real.log (625656742557 / 250000000000)) := by
  have h := reflection_log_11560_neg
  have he : Real.log (625656742557 / 250000000000) = -Real.log (250000000000 / 625656742557) := by
    rw [show ((625656742557 / 250000000000) : ℝ) = ((250000000000 / 625656742557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11561_neg : (89418611 / 250000000) ≤ -Real.log (100 / 143) ∧
    -Real.log (100 / 143) ≤ (71534889 / 200000000) := by
  have h := checkLog_sound (w := (43 / 243)) (n := 12)
    (lo := (89418611 / 250000000)) (hi := (71534889 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143 / 100) = 1/(100 / 143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11561 : Bounds (89418611 / 250000000) (71534889 / 200000000) (Real.log (143 / 100)) := by
  have h := reflection_log_11561_neg
  have he : Real.log (143 / 100) = -Real.log (100 / 143) := by
    rw [show ((143 / 100) : ℝ) = ((100 / 143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11562_neg : (281059459 / 500000000) ≤ -Real.log (57 / 100) ∧
    -Real.log (57 / 100) ≤ (562118919 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 157)) (n := 12)
    (lo := (281059459 / 500000000)) (hi := (562118919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 57) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 57) = 1/(57 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11562 : Bounds (-562118919 / 1000000000) (-281059459 / 500000000) (Real.log (57 / 100)) := by
  have h := reflection_log_11562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11563_neg : (429907 / 1000000000) ≤ -Real.log (100000 / 100043) ∧
    -Real.log (100000 / 100043) ≤ (107477 / 250000000) := by
  have h := checkLog_sound (w := (43 / 200043)) (n := 12)
    (lo := (429907 / 1000000000)) (hi := (107477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100043 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100043 / 100000) = 1/(100000 / 100043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11563 : Bounds (429907 / 1000000000) (107477 / 250000000) (Real.log (100043 / 100000)) := by
  have h := reflection_log_11563_neg
  have he : Real.log (100043 / 100000) = -Real.log (100000 / 100043) := by
    rw [show ((100043 / 100000) : ℝ) = ((100000 / 100043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11564_neg : (107523 / 250000000) ≤ -Real.log (99957 / 100000) ∧
    -Real.log (99957 / 100000) ≤ (430093 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 199957)) (n := 12)
    (lo := (107523 / 250000000)) (hi := (430093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99957) = 1/(99957 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11564 : Bounds (-430093 / 1000000000) (-107523 / 250000000) (Real.log (99957 / 100000)) := by
  have h := reflection_log_11564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11565_neg : (200348097 / 1000000000) ≤ -Real.log (250000 / 305457) ∧
    -Real.log (250000 / 305457) ≤ (100174049 / 500000000) := by
  have h := checkLog_sound (w := (55457 / 555457)) (n := 12)
    (lo := (200348097 / 1000000000)) (hi := (100174049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305457 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305457 / 250000) = 1/(250000 / 305457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11565 : Bounds (200348097 / 1000000000) (100174049 / 500000000) (Real.log (305457 / 250000)) := by
  have h := reflection_log_11565_neg
  have he : Real.log (305457 / 250000) = -Real.log (250000 / 305457) := by
    rw [show ((305457 / 250000) : ℝ) = ((250000 / 305457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11566_neg : (250807699 / 1000000000) ≤ -Real.log (194543 / 250000) ∧
    -Real.log (194543 / 250000) ≤ (2508077 / 10000000) := by
  have h := checkLog_sound (w := (55457 / 444543)) (n := 12)
    (lo := (250807699 / 1000000000)) (hi := (2508077 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 194543) = 1/(194543 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11566 : Bounds (-2508077 / 10000000) (-250807699 / 1000000000) (Real.log (194543 / 250000)) := by
  have h := reflection_log_11566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11567_neg : (8045667 / 40000000) ≤ -Real.log (500000 / 611399) ∧
    -Real.log (500000 / 611399) ≤ (50285419 / 250000000) := by
  have h := checkLog_sound (w := (111399 / 1111399)) (n := 12)
    (lo := (8045667 / 40000000)) (hi := (50285419 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611399 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611399 / 500000) = 1/(500000 / 611399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11567 : Bounds (8045667 / 40000000) (50285419 / 250000000) (Real.log (611399 / 500000)) := by
  have h := reflection_log_11567_neg
  have he : Real.log (611399 / 500000) = -Real.log (500000 / 611399) := by
    rw [show ((611399 / 500000) : ℝ) = ((500000 / 611399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11568_neg : (63013747 / 250000000) ≤ -Real.log (388601 / 500000) ∧
    -Real.log (388601 / 500000) ≤ (252054989 / 1000000000) := by
  have h := checkLog_sound (w := (111399 / 888601)) (n := 12)
    (lo := (63013747 / 250000000)) (hi := (252054989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 388601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 388601) = 1/(388601 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11568 : Bounds (-252054989 / 1000000000) (-63013747 / 250000000) (Real.log (388601 / 500000)) := by
  have h := reflection_log_11568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11569_neg : (1591041 / 31250000) ≤ -Real.log (237590262799 / 250000000000) ∧
    -Real.log (237590262799 / 250000000000) ≤ (50913313 / 1000000000) := by
  have h := checkLog_sound (w := (12409737201 / 487590262799)) (n := 12)
    (lo := (1591041 / 31250000)) (hi := (50913313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237590262799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237590262799) = 1/(237590262799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11569 : Bounds (-50913313 / 1000000000) (-1591041 / 31250000) (Real.log (237590262799 / 250000000000)) := by
  have h := reflection_log_11569_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11570_neg : (50459601 / 1000000000) ≤ -Real.log (59424521151 / 62500000000) ∧
    -Real.log (59424521151 / 62500000000) ≤ (25229801 / 500000000) := by
  have h := checkLog_sound (w := (3075478849 / 121924521151)) (n := 12)
    (lo := (50459601 / 1000000000)) (hi := (25229801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59424521151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59424521151) = 1/(59424521151 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11570 : Bounds (-25229801 / 500000000) (-50459601 / 1000000000) (Real.log (59424521151 / 62500000000)) := by
  have h := reflection_log_11570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11571_neg : (451155797 / 1000000000) ≤ -Real.log (250000000000 / 392531471191) ∧
    -Real.log (250000000000 / 392531471191) ≤ (225577899 / 500000000) := by
  have h := checkLog_sound (w := (142531471191 / 642531471191)) (n := 12)
    (lo := (451155797 / 1000000000)) (hi := (225577899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392531471191 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392531471191 / 250000000000) = 1/(250000000000 / 392531471191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11571 : Bounds (451155797 / 1000000000) (225577899 / 500000000) (Real.log (392531471191 / 250000000000)) := by
  have h := reflection_log_11571_neg
  have he : Real.log (392531471191 / 250000000000) = -Real.log (250000000000 / 392531471191) := by
    rw [show ((392531471191 / 250000000000) : ℝ) = ((250000000000 / 392531471191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11572_neg : (453196663 / 1000000000) ≤ -Real.log (125000000000 / 196666696689) ∧
    -Real.log (125000000000 / 196666696689) ≤ (56649583 / 125000000) := by
  have h := checkLog_sound (w := (71666696689 / 321666696689)) (n := 12)
    (lo := (453196663 / 1000000000)) (hi := (56649583 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196666696689 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196666696689 / 125000000000) = 1/(125000000000 / 196666696689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11572 : Bounds (453196663 / 1000000000) (56649583 / 125000000) (Real.log (196666696689 / 125000000000)) := by
  have h := reflection_log_11572_neg
  have he : Real.log (196666696689 / 125000000000) = -Real.log (125000000000 / 196666696689) := by
    rw [show ((196666696689 / 125000000000) : ℝ) = ((125000000000 / 196666696689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11573_neg : (917340967 / 1000000000) ≤ -Real.log (500000000000 / 1251313485113) ∧
    -Real.log (500000000000 / 1251313485113) ≤ (917340969 / 1000000000) := by
  have h := checkLog_sound (w := (251313485113 / 2251313485113)) (n := 12)
    (lo := (224193787 / 1000000000)) (hi := (56048447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251313485113 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1251313485113 / 1000000000000) = 1/(500000000000 / 1251313485113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11573 : Bounds (917340967 / 1000000000) (917340969 / 1000000000) (Real.log (1251313485113 / 500000000000)) := by
  have h := reflection_log_11573_neg
  have he : Real.log (1251313485113 / 500000000000) = -Real.log (500000000000 / 1251313485113) := by
    rw [show ((1251313485113 / 500000000000) : ℝ) = ((500000000000 / 1251313485113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11574_neg : (919793361 / 1000000000) ≤ -Real.log (500000000000 / 1254385964913) ∧
    -Real.log (500000000000 / 1254385964913) ≤ (919793363 / 1000000000) := by
  have h := checkLog_sound (w := (254385964913 / 2254385964913)) (n := 12)
    (lo := (226646181 / 1000000000)) (hi := (113323091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254385964913 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1254385964913 / 1000000000000) = 1/(500000000000 / 1254385964913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11574 : Bounds (919793361 / 1000000000) (919793363 / 1000000000) (Real.log (1254385964913 / 500000000000)) := by
  have h := reflection_log_11574_neg
  have he : Real.log (1254385964913 / 500000000000) = -Real.log (500000000000 / 1254385964913) := by
    rw [show ((1254385964913 / 500000000000) : ℝ) = ((500000000000 / 1254385964913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11575_neg : (716747 / 2000000) ≤ -Real.log (1000 / 1431) ∧
    -Real.log (1000 / 1431) ≤ (358373501 / 1000000000) := by
  have h := checkLog_sound (w := (431 / 2431)) (n := 12)
    (lo := (716747 / 2000000)) (hi := (358373501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1431 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1431 / 1000) = 1/(1000 / 1431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11575 : Bounds (716747 / 2000000) (358373501 / 1000000000) (Real.log (1431 / 1000)) := by
  have h := reflection_log_11575_neg
  have he : Real.log (1431 / 1000) = -Real.log (1000 / 1431) := by
    rw [show ((1431 / 1000) : ℝ) = ((1000 / 1431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11576_neg : (140968711 / 250000000) ≤ -Real.log (569 / 1000) ∧
    -Real.log (569 / 1000) ≤ (112774969 / 200000000) := by
  have h := checkLog_sound (w := (431 / 1569)) (n := 12)
    (lo := (140968711 / 250000000)) (hi := (112774969 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 569) = 1/(569 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11576 : Bounds (-112774969 / 200000000) (-140968711 / 250000000) (Real.log (569 / 1000)) := by
  have h := reflection_log_11576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11577_neg : (430907 / 1000000000) ≤ -Real.log (1000000 / 1000431) ∧
    -Real.log (1000000 / 1000431) ≤ (107727 / 250000000) := by
  have h := checkLog_sound (w := (431 / 2000431)) (n := 12)
    (lo := (430907 / 1000000000)) (hi := (107727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000431 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000431 / 1000000) = 1/(1000000 / 1000431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11577 : Bounds (430907 / 1000000000) (107727 / 250000000) (Real.log (1000431 / 1000000)) := by
  have h := reflection_log_11577_neg
  have he : Real.log (1000431 / 1000000) = -Real.log (1000000 / 1000431) := by
    rw [show ((1000431 / 1000000) : ℝ) = ((1000000 / 1000431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11578_neg : (107773 / 250000000) ≤ -Real.log (999569 / 1000000) ∧
    -Real.log (999569 / 1000000) ≤ (431093 / 1000000000) := by
  have h := checkLog_sound (w := (431 / 1999569)) (n := 12)
    (lo := (107773 / 250000000)) (hi := (431093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999569) = 1/(999569 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11578 : Bounds (-431093 / 1000000000) (-107773 / 250000000) (Real.log (999569 / 1000000)) := by
  have h := reflection_log_11578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11579_neg : (25100279 / 125000000) ≤ -Real.log (1000000 / 1222383) ∧
    -Real.log (1000000 / 1222383) ≤ (200802233 / 1000000000) := by
  have h := checkLog_sound (w := (222383 / 2222383)) (n := 12)
    (lo := (25100279 / 125000000)) (hi := (200802233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1222383 / 1000000) = 1/(1000000 / 1222383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11579 : Bounds (25100279 / 125000000) (200802233 / 1000000000) (Real.log (1222383 / 1000000)) := by
  have h := reflection_log_11579_neg
  have he : Real.log (1222383 / 1000000) = -Real.log (1000000 / 1222383) := by
    rw [show ((1222383 / 1000000) : ℝ) = ((1000000 / 1222383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11580_neg : (251521163 / 1000000000) ≤ -Real.log (777617 / 1000000) ∧
    -Real.log (777617 / 1000000) ≤ (62880291 / 250000000) := by
  have h := checkLog_sound (w := (222383 / 1777617)) (n := 12)
    (lo := (251521163 / 1000000000)) (hi := (62880291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 777617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 777617) = 1/(777617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11580 : Bounds (-62880291 / 250000000) (-251521163 / 1000000000) (Real.log (777617 / 1000000)) := by
  have h := reflection_log_11580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11581_neg : (100798133 / 500000000) ≤ -Real.log (500000 / 611677) ∧
    -Real.log (500000 / 611677) ≤ (201596267 / 1000000000) := by
  have h := checkLog_sound (w := (111677 / 1111677)) (n := 12)
    (lo := (100798133 / 500000000)) (hi := (201596267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611677 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611677 / 500000) = 1/(500000 / 611677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11581 : Bounds (100798133 / 500000000) (201596267 / 1000000000) (Real.log (611677 / 500000)) := by
  have h := reflection_log_11581_neg
  have he : Real.log (611677 / 500000) = -Real.log (500000 / 611677) := by
    rw [show ((611677 / 500000) : ℝ) = ((500000 / 611677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11582_neg : (25277063 / 100000000) ≤ -Real.log (388323 / 500000) ∧
    -Real.log (388323 / 500000) ≤ (252770631 / 1000000000) := by
  have h := checkLog_sound (w := (111677 / 888323)) (n := 12)
    (lo := (25277063 / 100000000)) (hi := (252770631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 388323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 388323) = 1/(388323 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11582 : Bounds (-252770631 / 1000000000) (-25277063 / 100000000) (Real.log (388323 / 500000)) := by
  have h := reflection_log_11582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11583_neg : (51174363 / 1000000000) ≤ -Real.log (237528247671 / 250000000000) ∧
    -Real.log (237528247671 / 250000000000) ≤ (12793591 / 250000000) := by
  have h := checkLog_sound (w := (12471752329 / 487528247671)) (n := 12)
    (lo := (51174363 / 1000000000)) (hi := (12793591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237528247671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237528247671) = 1/(237528247671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11583 : Bounds (-12793591 / 250000000) (-51174363 / 1000000000) (Real.log (237528247671 / 250000000000)) := by
  have h := reflection_log_11583_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
