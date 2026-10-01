import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0173
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

theorem reflection_log_1_neg : (127100303 / 200000000) ≤ -Real.log (6400 / 12083) ∧
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


theorem reflection_log_1 : Bounds (127100303 / 200000000) (158875379 / 250000000) (Real.log (12083 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12083 / 6400) = -Real.log (6400 / 12083) := by
    rw [show ((12083 / 6400) : ℝ) = ((6400 / 12083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2188977427 / 1000000000) ≤ -Real.log (717 / 6400) ∧
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


theorem reflection_log_2 : Bounds (-2188977431 / 1000000000) (-2188977427 / 1000000000) (Real.log (717 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (634714977 / 1000000000) ≤ -Real.log (12800 / 24147) ∧
    -Real.log (12800 / 24147) ≤ (317357489 / 500000000) := by
  have h := checkLog_sound (w := (11347 / 36947)) (n := 12)
    (lo := (634714977 / 1000000000)) (hi := (317357489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24147 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24147 / 12800) = 1/(12800 / 24147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (634714977 / 1000000000) (317357489 / 500000000) (Real.log (24147 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24147 / 12800) = -Real.log (12800 / 24147) := by
    rw [show ((24147 / 12800) : ℝ) = ((12800 / 24147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (16998553 / 7812500) ≤ -Real.log (1453 / 12800) ∧
    -Real.log (1453 / 12800) ≤ (543953697 / 250000000) := by
  have h := checkLog_sound (w := (147 / 3053)) (n := 12)
    (lo := (24093311 / 250000000)) (hi := (19274649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1453) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1453) = 1/(1453 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-543953697 / 250000000) (-16998553 / 7812500) (Real.log (1453 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (143582113 / 250000000) ≤ -Real.log (3200 / 5683) ∧
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


theorem reflection_log_5 : Bounds (143582113 / 250000000) (574328453 / 1000000000) (Real.log (5683 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5683 / 3200) = -Real.log (3200 / 5683) := by
    rw [show ((5683 / 3200) : ℝ) = ((3200 / 5683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1495830247 / 1000000000) ≤ -Real.log (717 / 3200) ∧
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


theorem reflection_log_6 : Bounds (-5983321 / 4000000) (-1495830247 / 1000000000) (Real.log (717 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (572655401 / 1000000000) ≤ -Real.log (6400 / 11347) ∧
    -Real.log (6400 / 11347) ≤ (286327701 / 500000000) := by
  have h := checkLog_sound (w := (4947 / 17747)) (n := 12)
    (lo := (572655401 / 1000000000)) (hi := (286327701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11347 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11347 / 6400) = 1/(6400 / 11347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (572655401 / 1000000000) (286327701 / 500000000) (Real.log (11347 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11347 / 6400) = -Real.log (6400 / 11347) := by
    rw [show ((11347 / 6400) : ℝ) = ((6400 / 11347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (370666901 / 250000000) ≤ -Real.log (1453 / 6400) ∧
    -Real.log (1453 / 6400) ≤ (1482667607 / 1000000000) := by
  have h := checkLog_sound (w := (147 / 3053)) (n := 12)
    (lo := (24093311 / 250000000)) (hi := (19274649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1453) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1453) = 1/(1453 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1482667607 / 1000000000) (-370666901 / 250000000) (Real.log (1453 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (649350453 / 1000000000) ≤ -Real.log (1000000 / 1914297) ∧
    -Real.log (1000000 / 1914297) ≤ (324675227 / 500000000) := by
  have h := checkLog_sound (w := (914297 / 2914297)) (n := 12)
    (lo := (649350453 / 1000000000)) (hi := (324675227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1914297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1914297 / 1000000) = 1/(1000000 / 1914297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (649350453 / 1000000000) (324675227 / 500000000) (Real.log (1914297 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1914297 / 1000000) = -Real.log (1000000 / 1914297) := by
    rw [show ((1914297 / 1000000) : ℝ) = ((1000000 / 1914297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1228433723 / 500000000) ≤ -Real.log (85703 / 1000000) ∧
    -Real.log (85703 / 1000000) ≤ (49137349 / 20000000) := by
  have h := checkLog_sound (w := (39297 / 210703)) (n := 12)
    (lo := (188712953 / 500000000)) (hi := (377425907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 85703) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 85703) = 1/(85703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-49137349 / 20000000) (-1228433723 / 500000000) (Real.log (85703 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (64986487 / 100000000) ≤ -Real.log (500000 / 957641) ∧
    -Real.log (500000 / 957641) ≤ (649864871 / 1000000000) := by
  have h := checkLog_sound (w := (457641 / 1457641)) (n := 12)
    (lo := (64986487 / 100000000)) (hi := (649864871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((957641 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(957641 / 500000) = 1/(500000 / 957641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (64986487 / 100000000) (649864871 / 1000000000) (Real.log (957641 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (957641 / 500000) = -Real.log (500000 / 957641) := by
    rw [show ((957641 / 500000) : ℝ) = ((500000 / 957641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2468427183 / 1000000000) ≤ -Real.log (42359 / 500000) ∧
    -Real.log (42359 / 500000) ≤ (2468427187 / 1000000000) := by
  have h := checkLog_sound (w := (20141 / 104859)) (n := 12)
    (lo := (388985643 / 1000000000)) (hi := (97246411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42359) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 42359) = 1/(42359 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2468427187 / 1000000000) (-2468427183 / 1000000000) (Real.log (42359 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (323842897 / 500000000) ≤ -Real.log (1000000 / 1911113) ∧
    -Real.log (1000000 / 1911113) ≤ (129537159 / 200000000) := by
  have h := checkLog_sound (w := (911113 / 2911113)) (n := 12)
    (lo := (323842897 / 500000000)) (hi := (129537159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1911113 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1911113 / 1000000) = 1/(1000000 / 1911113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (323842897 / 500000000) (129537159 / 200000000) (Real.log (1911113 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1911113 / 1000000) = -Real.log (1000000 / 1911113) := by
    rw [show ((1911113 / 1000000) : ℝ) = ((1000000 / 1911113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2420389377 / 1000000000) ≤ -Real.log (88887 / 1000000) ∧
    -Real.log (88887 / 1000000) ≤ (2420389381 / 1000000000) := by
  have h := checkLog_sound (w := (36113 / 213887)) (n := 12)
    (lo := (340947837 / 1000000000)) (hi := (170473919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88887) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 88887) = 1/(88887 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2420389381 / 1000000000) (-2420389377 / 1000000000) (Real.log (88887 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (162062949 / 250000000) ≤ -Real.log (200000 / 382439) ∧
    -Real.log (200000 / 382439) ≤ (648251797 / 1000000000) := by
  have h := checkLog_sound (w := (182439 / 582439)) (n := 12)
    (lo := (162062949 / 250000000)) (hi := (648251797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382439 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(382439 / 200000) = 1/(200000 / 382439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (162062949 / 250000000) (648251797 / 1000000000) (Real.log (382439 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (382439 / 200000) = -Real.log (200000 / 382439) := by
    rw [show ((382439 / 200000) : ℝ) = ((200000 / 382439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (243263683 / 100000000) ≤ -Real.log (17561 / 200000) ∧
    -Real.log (17561 / 200000) ≤ (1216318417 / 500000000) := by
  have h := checkLog_sound (w := (7439 / 42561)) (n := 12)
    (lo := (35319529 / 100000000)) (hi := (353195291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17561) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 17561) = 1/(17561 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1216318417 / 500000000) (-243263683 / 100000000) (Real.log (17561 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3106217899 / 1000000000) ≤ -Real.log (500000000000 / 11168202980059) ∧
    -Real.log (500000000000 / 11168202980059) ≤ (194138619 / 62500000) := by
  have h := checkLog_sound (w := (3168202980059 / 19168202980059)) (n := 12)
    (lo := (333629179 / 1000000000)) (hi := (16681459 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11168202980059 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11168202980059 / 8000000000000) = 1/(500000000000 / 11168202980059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3106217899 / 1000000000) (194138619 / 62500000) (Real.log (11168202980059 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11168202980059 / 500000000000) = -Real.log (500000000000 / 11168202980059) := by
    rw [show ((11168202980059 / 500000000000) : ℝ) = ((500000000000 / 11168202980059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3118292053 / 1000000000) ≤ -Real.log (125000000000 / 2825966736703) ∧
    -Real.log (125000000000 / 2825966736703) ≤ (1559146029 / 500000000) := by
  have h := checkLog_sound (w := (825966736703 / 4825966736703)) (n := 12)
    (lo := (345703333 / 1000000000)) (hi := (172851667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2825966736703 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2825966736703 / 2000000000000) = 1/(125000000000 / 2825966736703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3118292053 / 1000000000) (1559146029 / 500000000) (Real.log (2825966736703 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2825966736703 / 125000000000) = -Real.log (125000000000 / 2825966736703) := by
    rw [show ((2825966736703 / 125000000000) : ℝ) = ((125000000000 / 2825966736703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3068075171 / 1000000000) ≤ -Real.log (25000000000 / 537511953379) ∧
    -Real.log (25000000000 / 537511953379) ≤ (383509397 / 125000000) := by
  have h := checkLog_sound (w := (137511953379 / 937511953379)) (n := 12)
    (lo := (295486451 / 1000000000)) (hi := (73871613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537511953379 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(537511953379 / 400000000000) = 1/(25000000000 / 537511953379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3068075171 / 1000000000) (383509397 / 125000000) (Real.log (537511953379 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (537511953379 / 25000000000) = -Real.log (25000000000 / 537511953379) := by
    rw [show ((537511953379 / 25000000000) : ℝ) = ((25000000000 / 537511953379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1540444313 / 500000000) ≤ -Real.log (50000000000 / 1088887307101) ∧
    -Real.log (50000000000 / 1088887307101) ≤ (3080888631 / 1000000000) := by
  have h := checkLog_sound (w := (288887307101 / 1888887307101)) (n := 12)
    (lo := (154149953 / 500000000)) (hi := (308299907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088887307101 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1088887307101 / 800000000000) = 1/(50000000000 / 1088887307101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1540444313 / 500000000) (3080888631 / 1000000000) (Real.log (1088887307101 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1088887307101 / 50000000000) = -Real.log (50000000000 / 1088887307101) := by
    rw [show ((1088887307101 / 50000000000) : ℝ) = ((50000000000 / 1088887307101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0173
