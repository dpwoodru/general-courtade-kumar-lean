import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0391
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

theorem reflection_log_1_neg : (50595663 / 250000000) ≤ -Real.log (10240 / 12537) ∧
    -Real.log (10240 / 12537) ≤ (202382653 / 1000000000) := by
  have h := checkLog_sound (w := (2297 / 22777)) (n := 12)
    (lo := (50595663 / 250000000)) (hi := (202382653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12537 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12537 / 10240) = 1/(10240 / 12537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (50595663 / 250000000) (202382653 / 1000000000) (Real.log (12537 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12537 / 10240) = -Real.log (10240 / 12537) := by
    rw [show ((12537 / 10240) : ℝ) = ((10240 / 12537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (254010581 / 1000000000) ≤ -Real.log (7943 / 10240) ∧
    -Real.log (7943 / 10240) ≤ (127005291 / 500000000) := by
  have h := checkLog_sound (w := (2297 / 18183)) (n := 12)
    (lo := (254010581 / 1000000000)) (hi := (127005291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7943) = 1/(7943 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-127005291 / 500000000) (-254010581 / 1000000000) (Real.log (7943 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (50535833 / 250000000) ≤ -Real.log (5120 / 6267) ∧
    -Real.log (5120 / 6267) ≤ (202143333 / 1000000000) := by
  have h := checkLog_sound (w := (1147 / 11387)) (n := 12)
    (lo := (50535833 / 250000000)) (hi := (202143333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6267 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6267 / 5120) = 1/(5120 / 6267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (50535833 / 250000000) (202143333 / 1000000000) (Real.log (6267 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6267 / 5120) = -Real.log (5120 / 6267) := by
    rw [show ((6267 / 5120) : ℝ) = ((5120 / 6267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (126816481 / 500000000) ≤ -Real.log (3973 / 5120) ∧
    -Real.log (3973 / 5120) ≤ (253632963 / 1000000000) := by
  have h := checkLog_sound (w := (1147 / 9093)) (n := 12)
    (lo := (126816481 / 500000000)) (hi := (253632963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3973) = 1/(3973 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-253632963 / 1000000000) (-126816481 / 500000000) (Real.log (3973 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (370620223 / 1000000000) ≤ -Real.log (5120 / 7417) ∧
    -Real.log (5120 / 7417) ≤ (5790941 / 15625000) := by
  have h := checkLog_sound (w := (2297 / 12537)) (n := 12)
    (lo := (370620223 / 1000000000)) (hi := (5790941 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7417 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7417 / 5120) = 1/(5120 / 7417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (370620223 / 1000000000) (5790941 / 15625000) (Real.log (7417 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7417 / 5120) = -Real.log (5120 / 7417) := by
    rw [show ((7417 / 5120) : ℝ) = ((5120 / 7417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (595354289 / 1000000000) ≤ -Real.log (2823 / 5120) ∧
    -Real.log (2823 / 5120) ≤ (59535429 / 100000000) := by
  have h := checkLog_sound (w := (2297 / 7943)) (n := 12)
    (lo := (595354289 / 1000000000)) (hi := (59535429 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2823) = 1/(2823 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-59535429 / 100000000) (-595354289 / 1000000000) (Real.log (2823 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (74043133 / 200000000) ≤ -Real.log (2560 / 3707) ∧
    -Real.log (2560 / 3707) ≤ (185107833 / 500000000) := by
  have h := checkLog_sound (w := (1147 / 6267)) (n := 12)
    (lo := (74043133 / 200000000)) (hi := (185107833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3707 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3707 / 2560) = 1/(2560 / 3707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (74043133 / 200000000) (185107833 / 500000000) (Real.log (3707 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3707 / 2560) = -Real.log (2560 / 3707) := by
    rw [show ((3707 / 2560) : ℝ) = ((2560 / 3707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (297146077 / 500000000) ≤ -Real.log (1413 / 2560) ∧
    -Real.log (1413 / 2560) ≤ (118858431 / 200000000) := by
  have h := checkLog_sound (w := (1147 / 3973)) (n := 12)
    (lo := (297146077 / 500000000)) (hi := (118858431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1413) = 1/(1413 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-118858431 / 200000000) (-297146077 / 500000000) (Real.log (1413 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (138707523 / 500000000) ≤ -Real.log (500000 / 659857) ∧
    -Real.log (500000 / 659857) ≤ (277415047 / 1000000000) := by
  have h := checkLog_sound (w := (159857 / 1159857)) (n := 12)
    (lo := (138707523 / 500000000)) (hi := (277415047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659857 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659857 / 500000) = 1/(500000 / 659857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (138707523 / 500000000) (277415047 / 1000000000) (Real.log (659857 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (659857 / 500000) = -Real.log (500000 / 659857) := by
    rw [show ((659857 / 500000) : ℝ) = ((500000 / 659857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (19262099 / 50000000) ≤ -Real.log (340143 / 500000) ∧
    -Real.log (340143 / 500000) ≤ (385241981 / 1000000000) := by
  have h := checkLog_sound (w := (159857 / 840143)) (n := 12)
    (lo := (19262099 / 50000000)) (hi := (385241981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 340143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 340143) = 1/(340143 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-385241981 / 1000000000) (-19262099 / 50000000) (Real.log (340143 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (277738549 / 1000000000) ≤ -Real.log (1000000 / 1320141) ∧
    -Real.log (1000000 / 1320141) ≤ (5554771 / 20000000) := by
  have h := checkLog_sound (w := (320141 / 2320141)) (n := 12)
    (lo := (277738549 / 1000000000)) (hi := (5554771 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1320141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1320141 / 1000000) = 1/(1000000 / 1320141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (277738549 / 1000000000) (5554771 / 20000000) (Real.log (1320141 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1320141 / 1000000) = -Real.log (1000000 / 1320141) := by
    rw [show ((1320141 / 1000000) : ℝ) = ((1000000 / 1320141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (77173971 / 200000000) ≤ -Real.log (679859 / 1000000) ∧
    -Real.log (679859 / 1000000) ≤ (12058433 / 31250000) := by
  have h := checkLog_sound (w := (320141 / 1679859)) (n := 12)
    (lo := (77173971 / 200000000)) (hi := (12058433 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 679859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 679859) = 1/(679859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-12058433 / 31250000) (-77173971 / 200000000) (Real.log (679859 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (209170379 / 1000000000) ≤ -Real.log (200000 / 246531) ∧
    -Real.log (200000 / 246531) ≤ (10458519 / 50000000) := by
  have h := checkLog_sound (w := (46531 / 446531)) (n := 12)
    (lo := (209170379 / 1000000000)) (hi := (10458519 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246531 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246531 / 200000) = 1/(200000 / 246531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (209170379 / 1000000000) (10458519 / 50000000) (Real.log (246531 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (246531 / 200000) = -Real.log (200000 / 246531) := by
    rw [show ((246531 / 200000) : ℝ) = ((200000 / 246531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (132409387 / 500000000) ≤ -Real.log (153469 / 200000) ∧
    -Real.log (153469 / 200000) ≤ (10592751 / 40000000) := by
  have h := checkLog_sound (w := (46531 / 353469)) (n := 12)
    (lo := (132409387 / 500000000)) (hi := (10592751 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 153469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 153469) = 1/(153469 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10592751 / 40000000) (-132409387 / 500000000) (Real.log (153469 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (209437247 / 1000000000) ≤ -Real.log (125000 / 154123) ∧
    -Real.log (125000 / 154123) ≤ (3272457 / 15625000) := by
  have h := checkLog_sound (w := (29123 / 279123)) (n := 12)
    (lo := (209437247 / 1000000000)) (hi := (3272457 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154123 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154123 / 125000) = 1/(125000 / 154123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (209437247 / 1000000000) (3272457 / 15625000) (Real.log (154123 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (154123 / 125000) = -Real.log (125000 / 154123) := by
    rw [show ((154123 / 125000) : ℝ) = ((125000 / 154123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (265247617 / 1000000000) ≤ -Real.log (95877 / 125000) ∧
    -Real.log (95877 / 125000) ≤ (132623809 / 500000000) := by
  have h := checkLog_sound (w := (29123 / 220877)) (n := 12)
    (lo := (265247617 / 1000000000)) (hi := (132623809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 95877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 95877) = 1/(95877 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-132623809 / 500000000) (-265247617 / 1000000000) (Real.log (95877 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (662657027 / 1000000000) ≤ -Real.log (125000000000 / 242492495803) ∧
    -Real.log (125000000000 / 242492495803) ≤ (165664257 / 250000000) := by
  have h := checkLog_sound (w := (117492495803 / 367492495803)) (n := 12)
    (lo := (662657027 / 1000000000)) (hi := (165664257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242492495803 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242492495803 / 125000000000) = 1/(125000000000 / 242492495803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (662657027 / 1000000000) (165664257 / 250000000) (Real.log (242492495803 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (242492495803 / 125000000000) = -Real.log (125000000000 / 242492495803) := by
    rw [show ((242492495803 / 125000000000) : ℝ) = ((125000000000 / 242492495803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (165902101 / 250000000) ≤ -Real.log (125000000000 / 242723307333) ∧
    -Real.log (125000000000 / 242723307333) ≤ (132721681 / 200000000) := by
  have h := checkLog_sound (w := (117723307333 / 367723307333)) (n := 12)
    (lo := (165902101 / 250000000)) (hi := (132721681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242723307333 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242723307333 / 125000000000) = 1/(125000000000 / 242723307333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (165902101 / 250000000) (132721681 / 200000000) (Real.log (242723307333 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (242723307333 / 125000000000) = -Real.log (125000000000 / 242723307333) := by
    rw [show ((242723307333 / 125000000000) : ℝ) = ((125000000000 / 242723307333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (473989153 / 1000000000) ≤ -Real.log (62500000000 / 100399347751) ∧
    -Real.log (62500000000 / 100399347751) ≤ (236994577 / 500000000) := by
  have h := checkLog_sound (w := (37899347751 / 162899347751)) (n := 12)
    (lo := (473989153 / 1000000000)) (hi := (236994577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100399347751 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100399347751 / 62500000000) = 1/(62500000000 / 100399347751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (473989153 / 1000000000) (236994577 / 500000000) (Real.log (100399347751 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (100399347751 / 62500000000) = -Real.log (62500000000 / 100399347751) := by
    rw [show ((100399347751 / 62500000000) : ℝ) = ((62500000000 / 100399347751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (7416951 / 15625000) ≤ -Real.log (500000000000 / 803753767849) ∧
    -Real.log (500000000000 / 803753767849) ≤ (94936973 / 200000000) := by
  have h := checkLog_sound (w := (303753767849 / 1303753767849)) (n := 12)
    (lo := (7416951 / 15625000)) (hi := (94936973 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803753767849 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803753767849 / 500000000000) = 1/(500000000000 / 803753767849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (7416951 / 15625000) (94936973 / 200000000) (Real.log (803753767849 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (803753767849 / 500000000000) = -Real.log (500000000000 / 803753767849) := by
    rw [show ((803753767849 / 500000000000) : ℝ) = ((500000000000 / 803753767849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0391
