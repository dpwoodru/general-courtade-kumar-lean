import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0172
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

theorem reflection_log_1_neg : (127257487 / 200000000) ≤ -Real.log (2560 / 4837) ∧
    -Real.log (2560 / 4837) ≤ (159071859 / 250000000) := by
  have h := checkLog_sound (w := (2277 / 7397)) (n := 12)
    (lo := (127257487 / 200000000)) (hi := (159071859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4837 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4837 / 2560) = 1/(2560 / 4837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (127257487 / 200000000) (159071859 / 250000000) (Real.log (4837 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (4837 / 2560) = -Real.log (2560 / 4837) := by
    rw [show ((4837 / 2560) : ℝ) = ((2560 / 4837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1101157819 / 500000000) ≤ -Real.log (283 / 2560) ∧
    -Real.log (283 / 2560) ≤ (1101157821 / 500000000) := by
  have h := checkLog_sound (w := (37 / 603)) (n := 12)
    (lo := (61437049 / 500000000)) (hi := (122874099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 283) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 283) = 1/(283 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1101157821 / 500000000) (-1101157819 / 500000000) (Real.log (283 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (127100303 / 200000000) ≤ -Real.log (6400 / 12083) ∧
    -Real.log (6400 / 12083) ≤ (158875379 / 250000000) := by
  have h := checkLog_sound (w := (5683 / 18483)) (n := 12)
    (lo := (127100303 / 200000000)) (hi := (158875379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12083 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12083 / 6400) = 1/(6400 / 12083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (127100303 / 200000000) (158875379 / 250000000) (Real.log (12083 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12083 / 6400) = -Real.log (6400 / 12083) := by
    rw [show ((12083 / 6400) : ℝ) = ((6400 / 12083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2188977427 / 1000000000) ≤ -Real.log (717 / 6400) ∧
    -Real.log (717 / 6400) ≤ (2188977431 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 1517)) (n := 12)
    (lo := (109535887 / 1000000000)) (hi := (6845993 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 717) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 717) = 1/(717 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2188977431 / 1000000000) (-2188977427 / 1000000000) (Real.log (717 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (575998709 / 1000000000) ≤ -Real.log (1280 / 2277) ∧
    -Real.log (1280 / 2277) ≤ (57599871 / 100000000) := by
  have h := checkLog_sound (w := (997 / 3557)) (n := 12)
    (lo := (575998709 / 1000000000)) (hi := (57599871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2277 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2277 / 1280) = 1/(1280 / 2277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (575998709 / 1000000000) (57599871 / 100000000) (Real.log (2277 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2277 / 1280) = -Real.log (1280 / 2277) := by
    rw [show ((2277 / 1280) : ℝ) = ((1280 / 2277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (754584229 / 500000000) ≤ -Real.log (283 / 1280) ∧
    -Real.log (283 / 1280) ≤ (1509168461 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 603)) (n := 12)
    (lo := (61437049 / 500000000)) (hi := (122874099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 283) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 283) = 1/(283 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1509168461 / 1000000000) (-754584229 / 500000000) (Real.log (283 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (143582113 / 250000000) ≤ -Real.log (3200 / 5683) ∧
    -Real.log (3200 / 5683) ≤ (574328453 / 1000000000) := by
  have h := checkLog_sound (w := (2483 / 8883)) (n := 12)
    (lo := (143582113 / 250000000)) (hi := (574328453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5683 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5683 / 3200) = 1/(3200 / 5683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (143582113 / 250000000) (574328453 / 1000000000) (Real.log (5683 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5683 / 3200) = -Real.log (3200 / 5683) := by
    rw [show ((5683 / 3200) : ℝ) = ((3200 / 5683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1495830247 / 1000000000) ≤ -Real.log (717 / 3200) ∧
    -Real.log (717 / 3200) ≤ (5983321 / 4000000) := by
  have h := checkLog_sound (w := (83 / 1517)) (n := 12)
    (lo := (109535887 / 1000000000)) (hi := (6845993 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 717) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 717) = 1/(717 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-5983321 / 4000000) (-1495830247 / 1000000000) (Real.log (717 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (162466087 / 250000000) ≤ -Real.log (1000000 / 1915281) ∧
    -Real.log (1000000 / 1915281) ≤ (649864349 / 1000000000) := by
  have h := checkLog_sound (w := (915281 / 2915281)) (n := 12)
    (lo := (162466087 / 250000000)) (hi := (649864349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1915281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1915281 / 1000000) = 1/(1000000 / 1915281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (162466087 / 250000000) (649864349 / 1000000000) (Real.log (1915281 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1915281 / 1000000) = -Real.log (1000000 / 1915281) := by
    rw [show ((1915281 / 1000000) : ℝ) = ((1000000 / 1915281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2468415379 / 1000000000) ≤ -Real.log (84719 / 1000000) ∧
    -Real.log (84719 / 1000000) ≤ (2468415383 / 1000000000) := by
  have h := checkLog_sound (w := (40281 / 209719)) (n := 12)
    (lo := (388973839 / 1000000000)) (hi := (4862173 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84719) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 84719) = 1/(84719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2468415383 / 1000000000) (-2468415379 / 1000000000) (Real.log (84719 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (325190033 / 500000000) ≤ -Real.log (1000000 / 1916269) ∧
    -Real.log (1000000 / 1916269) ≤ (650380067 / 1000000000) := by
  have h := checkLog_sound (w := (916269 / 2916269)) (n := 12)
    (lo := (325190033 / 500000000)) (hi := (650380067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1916269 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1916269 / 1000000) = 1/(1000000 / 1916269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (325190033 / 500000000) (650380067 / 1000000000) (Real.log (1916269 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1916269 / 1000000) = -Real.log (1000000 / 1916269) := by
    rw [show ((1916269 / 1000000) : ℝ) = ((1000000 / 1916269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1240072999 / 500000000) ≤ -Real.log (83731 / 1000000) ∧
    -Real.log (83731 / 1000000) ≤ (1240073001 / 500000000) := by
  have h := checkLog_sound (w := (41269 / 208731)) (n := 12)
    (lo := (200352229 / 500000000)) (hi := (400704459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 83731) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 83731) = 1/(83731 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1240073001 / 500000000) (-1240072999 / 500000000) (Real.log (83731 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (648251273 / 1000000000) ≤ -Real.log (500000 / 956097) ∧
    -Real.log (500000 / 956097) ≤ (324125637 / 500000000) := by
  have h := checkLog_sound (w := (456097 / 1456097)) (n := 12)
    (lo := (648251273 / 1000000000)) (hi := (324125637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((956097 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(956097 / 500000) = 1/(500000 / 956097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (648251273 / 1000000000) (324125637 / 500000000) (Real.log (956097 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (956097 / 500000) = -Real.log (500000 / 956097) := by
    rw [show ((956097 / 500000) : ℝ) = ((500000 / 956097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2432625441 / 1000000000) ≤ -Real.log (43903 / 500000) ∧
    -Real.log (43903 / 500000) ≤ (486525089 / 200000000) := by
  have h := checkLog_sound (w := (18597 / 106403)) (n := 12)
    (lo := (353183901 / 1000000000)) (hi := (176591951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43903) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 43903) = 1/(43903 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-486525089 / 200000000) (-2432625441 / 1000000000) (Real.log (43903 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (324408739 / 500000000) ≤ -Real.log (1000000 / 1913277) ∧
    -Real.log (1000000 / 1913277) ≤ (648817479 / 1000000000) := by
  have h := checkLog_sound (w := (913277 / 2913277)) (n := 12)
    (lo := (324408739 / 500000000)) (hi := (648817479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1913277 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1913277 / 1000000) = 1/(1000000 / 1913277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (324408739 / 500000000) (648817479 / 1000000000) (Real.log (1913277 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1913277 / 1000000) = -Real.log (1000000 / 1913277) := by
    rw [show ((1913277 / 1000000) : ℝ) = ((1000000 / 1913277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1222518073 / 500000000) ≤ -Real.log (86723 / 1000000) ∧
    -Real.log (86723 / 1000000) ≤ (48900723 / 20000000) := by
  have h := checkLog_sound (w := (38277 / 211723)) (n := 12)
    (lo := (182797303 / 500000000)) (hi := (365594607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86723) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 86723) = 1/(86723 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-48900723 / 20000000) (-1222518073 / 500000000) (Real.log (86723 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3118279727 / 1000000000) ≤ -Real.log (500000000000 / 11303727617181) ∧
    -Real.log (500000000000 / 11303727617181) ≤ (779569933 / 250000000) := by
  have h := checkLog_sound (w := (3303727617181 / 19303727617181)) (n := 12)
    (lo := (345691007 / 1000000000)) (hi := (2700711 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11303727617181 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11303727617181 / 8000000000000) = 1/(500000000000 / 11303727617181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3118279727 / 1000000000) (779569933 / 250000000) (Real.log (11303727617181 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11303727617181 / 500000000000) = -Real.log (500000000000 / 11303727617181) := by
    rw [show ((11303727617181 / 500000000000) : ℝ) = ((500000000000 / 11303727617181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3130526063 / 1000000000) ≤ -Real.log (500000000000 / 11443007965987) ∧
    -Real.log (500000000000 / 11443007965987) ≤ (782631517 / 250000000) := by
  have h := checkLog_sound (w := (3443007965987 / 19443007965987)) (n := 12)
    (lo := (357937343 / 1000000000)) (hi := (5592771 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11443007965987 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11443007965987 / 8000000000000) = 1/(500000000000 / 11443007965987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3130526063 / 1000000000) (782631517 / 250000000) (Real.log (11443007965987 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11443007965987 / 500000000000) = -Real.log (500000000000 / 11443007965987) := by
    rw [show ((11443007965987 / 500000000000) : ℝ) = ((500000000000 / 11443007965987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (616175343 / 200000000) ≤ -Real.log (62500000000 / 1361092920757) ∧
    -Real.log (62500000000 / 1361092920757) ≤ (38510959 / 12500000) := by
  have h := checkLog_sound (w := (361092920757 / 2361092920757)) (n := 12)
    (lo := (61657599 / 200000000)) (hi := (77071999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1361092920757 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1361092920757 / 1000000000000) = 1/(62500000000 / 1361092920757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (616175343 / 200000000) (38510959 / 12500000) (Real.log (1361092920757 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1361092920757 / 62500000000) = -Real.log (62500000000 / 1361092920757) := by
    rw [show ((1361092920757 / 62500000000) : ℝ) = ((62500000000 / 1361092920757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (386731703 / 125000000) ≤ -Real.log (100000000000 / 2206193282059) ∧
    -Real.log (100000000000 / 2206193282059) ≤ (3093853629 / 1000000000) := by
  have h := checkLog_sound (w := (606193282059 / 3806193282059)) (n := 12)
    (lo := (40158113 / 125000000)) (hi := (64252981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2206193282059 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2206193282059 / 1600000000000) = 1/(100000000000 / 2206193282059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (386731703 / 125000000) (3093853629 / 1000000000) (Real.log (2206193282059 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2206193282059 / 100000000000) = -Real.log (100000000000 / 2206193282059) := by
    rw [show ((2206193282059 / 100000000000) : ℝ) = ((100000000000 / 2206193282059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0172
