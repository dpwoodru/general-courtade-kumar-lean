import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0024
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

theorem reflection_log_1_neg : (395256931 / 1000000000) ≤ -Real.log (2560 / 3801) ∧
    -Real.log (2560 / 3801) ≤ (98814233 / 250000000) := by
  have h := checkLog_sound (w := (1241 / 6361)) (n := 12)
    (lo := (395256931 / 1000000000)) (hi := (98814233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3801 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3801 / 2560) = 1/(2560 / 3801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (395256931 / 1000000000) (98814233 / 250000000) (Real.log (3801 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3801 / 2560) = -Real.log (2560 / 3801) := by
    rw [show ((3801 / 2560) : ℝ) = ((2560 / 3801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (82891673 / 125000000) ≤ -Real.log (1319 / 2560) ∧
    -Real.log (1319 / 2560) ≤ (132626677 / 200000000) := by
  have h := checkLog_sound (w := (1241 / 3879)) (n := 12)
    (lo := (82891673 / 125000000)) (hi := (132626677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1319) = 1/(1319 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-132626677 / 200000000) (-82891673 / 125000000) (Real.log (1319 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (394467353 / 1000000000) ≤ -Real.log (1280 / 1899) ∧
    -Real.log (1280 / 1899) ≤ (197233677 / 500000000) := by
  have h := checkLog_sound (w := (619 / 3179)) (n := 12)
    (lo := (394467353 / 1000000000)) (hi := (197233677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1899 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1899 / 1280) = 1/(1280 / 1899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (394467353 / 1000000000) (197233677 / 500000000) (Real.log (1899 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1899 / 1280) = -Real.log (1280 / 1899) := by
    rw [show ((1899 / 1280) : ℝ) = ((1280 / 1899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (660861517 / 1000000000) ≤ -Real.log (661 / 1280) ∧
    -Real.log (661 / 1280) ≤ (330430759 / 500000000) := by
  have h := checkLog_sound (w := (619 / 1941)) (n := 12)
    (lo := (660861517 / 1000000000)) (hi := (330430759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 661) = 1/(661 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-330430759 / 500000000) (-660861517 / 1000000000) (Real.log (661 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (67779557 / 100000000) ≤ -Real.log (1280 / 2521) ∧
    -Real.log (1280 / 2521) ≤ (677795571 / 1000000000) := by
  have h := checkLog_sound (w := (1241 / 3801)) (n := 12)
    (lo := (67779557 / 100000000)) (hi := (677795571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2521 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2521 / 1280) = 1/(1280 / 2521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (67779557 / 100000000) (677795571 / 1000000000) (Real.log (2521 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2521 / 1280) = -Real.log (1280 / 2521) := by
    rw [show ((2521 / 1280) : ℝ) = ((1280 / 2521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3491053707 / 1000000000) ≤ -Real.log (39 / 1280) ∧
    -Real.log (39 / 1280) ≤ (3491053713 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 39) = 1/(39 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3491053713 / 1000000000) (-3491053707 / 1000000000) (Real.log (39 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (676604857 / 1000000000) ≤ -Real.log (640 / 1259) ∧
    -Real.log (640 / 1259) ≤ (338302429 / 500000000) := by
  have h := checkLog_sound (w := (619 / 1899)) (n := 12)
    (lo := (676604857 / 1000000000)) (hi := (338302429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259 / 640) = 1/(640 / 1259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (676604857 / 1000000000) (338302429 / 500000000) (Real.log (1259 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1259 / 640) = -Real.log (640 / 1259) := by
    rw [show ((1259 / 640) : ℝ) = ((640 / 1259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (427118217 / 125000000) ≤ -Real.log (21 / 640) ∧
    -Real.log (21 / 640) ≤ (3416945741 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 21) = 1/(21 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3416945741 / 1000000000) (-427118217 / 125000000) (Real.log (21 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (552648717 / 1000000000) ≤ -Real.log (20000 / 34757) ∧
    -Real.log (20000 / 34757) ≤ (276324359 / 500000000) := by
  have h := checkLog_sound (w := (14757 / 54757)) (n := 12)
    (lo := (552648717 / 1000000000)) (hi := (276324359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34757 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34757 / 20000) = 1/(20000 / 34757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (552648717 / 1000000000) (276324359 / 500000000) (Real.log (34757 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (34757 / 20000) = -Real.log (20000 / 34757) := by
    rw [show ((34757 / 20000) : ℝ) = ((20000 / 34757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1338838419 / 1000000000) ≤ -Real.log (5243 / 20000) ∧
    -Real.log (5243 / 20000) ≤ (1338838421 / 1000000000) := by
  have h := checkLog_sound (w := (4757 / 15243)) (n := 12)
    (lo := (645691239 / 1000000000)) (hi := (16142281 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 5243) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10000 / 5243) = 1/(5243 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1338838421 / 1000000000) (-1338838419 / 1000000000) (Real.log (5243 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (110823339 / 200000000) ≤ -Real.log (1000000 / 1740403) ∧
    -Real.log (1000000 / 1740403) ≤ (69264587 / 125000000) := by
  have h := checkLog_sound (w := (740403 / 2740403)) (n := 12)
    (lo := (110823339 / 200000000)) (hi := (69264587 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1740403 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1740403 / 1000000) = 1/(1000000 / 1740403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (110823339 / 200000000) (69264587 / 125000000) (Real.log (1740403 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1740403 / 1000000) = -Real.log (1000000 / 1740403) := by
    rw [show ((1740403 / 1000000) : ℝ) = ((1000000 / 1740403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1348624849 / 1000000000) ≤ -Real.log (259597 / 1000000) ∧
    -Real.log (259597 / 1000000) ≤ (1348624851 / 1000000000) := by
  have h := checkLog_sound (w := (240403 / 759597)) (n := 12)
    (lo := (655477669 / 1000000000)) (hi := (65547767 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 259597) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 259597) = 1/(259597 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1348624851 / 1000000000) (-1348624849 / 1000000000) (Real.log (259597 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (477643123 / 1000000000) ≤ -Real.log (100000 / 161227) ∧
    -Real.log (100000 / 161227) ≤ (119410781 / 250000000) := by
  have h := checkLog_sound (w := (61227 / 261227)) (n := 12)
    (lo := (477643123 / 1000000000)) (hi := (119410781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161227 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161227 / 100000) = 1/(100000 / 161227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (477643123 / 1000000000) (119410781 / 250000000) (Real.log (161227 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (161227 / 100000) = -Real.log (100000 / 161227) := by
    rw [show ((161227 / 100000) : ℝ) = ((100000 / 161227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (947446057 / 1000000000) ≤ -Real.log (38773 / 100000) ∧
    -Real.log (38773 / 100000) ≤ (947446059 / 1000000000) := by
  have h := checkLog_sound (w := (11227 / 88773)) (n := 12)
    (lo := (254298877 / 1000000000)) (hi := (127149439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 38773) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 38773) = 1/(38773 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-947446059 / 1000000000) (-947446057 / 1000000000) (Real.log (38773 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (47938511 / 100000000) ≤ -Real.log (1000000 / 1615081) ∧
    -Real.log (1000000 / 1615081) ≤ (479385111 / 1000000000) := by
  have h := checkLog_sound (w := (615081 / 2615081)) (n := 12)
    (lo := (47938511 / 100000000)) (hi := (479385111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1615081 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1615081 / 1000000) = 1/(1000000 / 1615081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (47938511 / 100000000) (479385111 / 1000000000) (Real.log (1615081 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1615081 / 1000000) = -Real.log (1000000 / 1615081) := by
    rw [show ((1615081 / 1000000) : ℝ) = ((1000000 / 1615081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (190944471 / 200000000) ≤ -Real.log (384919 / 1000000) ∧
    -Real.log (384919 / 1000000) ≤ (954722357 / 1000000000) := by
  have h := checkLog_sound (w := (115081 / 884919)) (n := 12)
    (lo := (10463007 / 40000000)) (hi := (32696897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384919) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 384919) = 1/(384919 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-954722357 / 1000000000) (-190944471 / 200000000) (Real.log (384919 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (378297427 / 200000000) ≤ -Real.log (500000000000 / 3314609956131) ∧
    -Real.log (500000000000 / 3314609956131) ≤ (945743569 / 500000000) := by
  have h := checkLog_sound (w := (1314609956131 / 5314609956131)) (n := 12)
    (lo := (20207711 / 40000000)) (hi := (63149097 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3314609956131 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3314609956131 / 2000000000000) = 1/(500000000000 / 3314609956131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (378297427 / 200000000) (945743569 / 500000000) (Real.log (3314609956131 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3314609956131 / 500000000000) = -Real.log (500000000000 / 3314609956131) := by
    rw [show ((3314609956131 / 500000000000) : ℝ) = ((500000000000 / 3314609956131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (237842693 / 125000000) ≤ -Real.log (100000000000 / 670424927869) ∧
    -Real.log (100000000000 / 670424927869) ≤ (1902741547 / 1000000000) := by
  have h := checkLog_sound (w := (270424927869 / 1070424927869)) (n := 12)
    (lo := (32277949 / 62500000)) (hi := (103289437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((670424927869 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(670424927869 / 400000000000) = 1/(100000000000 / 670424927869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (237842693 / 125000000) (1902741547 / 1000000000) (Real.log (670424927869 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (670424927869 / 100000000000) = -Real.log (100000000000 / 670424927869) := by
    rw [show ((670424927869 / 100000000000) : ℝ) = ((100000000000 / 670424927869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (71254459 / 50000000) ≤ -Real.log (250000000000 / 1039557166069) ∧
    -Real.log (250000000000 / 1039557166069) ≤ (1425089183 / 1000000000) := by
  have h := checkLog_sound (w := (39557166069 / 2039557166069)) (n := 12)
    (lo := (1939741 / 50000000)) (hi := (38794821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1039557166069 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1039557166069 / 1000000000000) = 1/(250000000000 / 1039557166069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (71254459 / 50000000) (1425089183 / 1000000000) (Real.log (1039557166069 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1039557166069 / 250000000000) = -Real.log (250000000000 / 1039557166069) := by
    rw [show ((1039557166069 / 250000000000) : ℝ) = ((250000000000 / 1039557166069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (286821493 / 200000000) ≤ -Real.log (500000000000 / 2097949178919) ∧
    -Real.log (500000000000 / 2097949178919) ≤ (358526867 / 250000000) := by
  have h := checkLog_sound (w := (97949178919 / 4097949178919)) (n := 12)
    (lo := (9562621 / 200000000)) (hi := (23906553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2097949178919 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2097949178919 / 2000000000000) = 1/(500000000000 / 2097949178919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (286821493 / 200000000) (358526867 / 250000000) (Real.log (2097949178919 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2097949178919 / 500000000000) = -Real.log (500000000000 / 2097949178919) := by
    rw [show ((2097949178919 / 500000000000) : ℝ) = ((500000000000 / 2097949178919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0024
