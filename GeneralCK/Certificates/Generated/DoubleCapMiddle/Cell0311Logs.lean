import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0311
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

theorem reflection_log_1_neg : (221345059 / 1000000000) ≤ -Real.log (10240 / 12777) ∧
    -Real.log (10240 / 12777) ≤ (11067253 / 50000000) := by
  have h := checkLog_sound (w := (2537 / 23017)) (n := 12)
    (lo := (221345059 / 1000000000)) (hi := (11067253 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12777 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12777 / 10240) = 1/(10240 / 12777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (221345059 / 1000000000) (11067253 / 50000000) (Real.log (12777 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12777 / 10240) = -Real.log (10240 / 12777) := by
    rw [show ((12777 / 10240) : ℝ) = ((10240 / 12777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (71172939 / 250000000) ≤ -Real.log (7703 / 10240) ∧
    -Real.log (7703 / 10240) ≤ (284691757 / 1000000000) := by
  have h := checkLog_sound (w := (2537 / 17943)) (n := 12)
    (lo := (71172939 / 250000000)) (hi := (284691757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7703) = 1/(7703 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-284691757 / 1000000000) (-71172939 / 250000000) (Real.log (7703 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (44222047 / 200000000) ≤ -Real.log (5120 / 6387) ∧
    -Real.log (5120 / 6387) ≤ (55277559 / 250000000) := by
  have h := checkLog_sound (w := (1267 / 11507)) (n := 12)
    (lo := (44222047 / 200000000)) (hi := (55277559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6387 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6387 / 5120) = 1/(5120 / 6387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (44222047 / 200000000) (55277559 / 250000000) (Real.log (6387 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6387 / 5120) = -Real.log (5120 / 6387) := by
    rw [show ((6387 / 5120) : ℝ) = ((5120 / 6387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (284302373 / 1000000000) ≤ -Real.log (3853 / 5120) ∧
    -Real.log (3853 / 5120) ≤ (142151187 / 500000000) := by
  have h := checkLog_sound (w := (1267 / 8973)) (n := 12)
    (lo := (284302373 / 1000000000)) (hi := (142151187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3853) = 1/(3853 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-142151187 / 500000000) (-284302373 / 1000000000) (Real.log (3853 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (402465823 / 1000000000) ≤ -Real.log (5120 / 7657) ∧
    -Real.log (5120 / 7657) ≤ (12577057 / 31250000) := by
  have h := checkLog_sound (w := (2537 / 12777)) (n := 12)
    (lo := (402465823 / 1000000000)) (hi := (12577057 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7657 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7657 / 5120) = 1/(5120 / 7657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (402465823 / 1000000000) (12577057 / 31250000) (Real.log (7657 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7657 / 5120) = -Real.log (5120 / 7657) := by
    rw [show ((7657 / 5120) : ℝ) = ((5120 / 7657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (171050731 / 250000000) ≤ -Real.log (2583 / 5120) ∧
    -Real.log (2583 / 5120) ≤ (27368117 / 40000000) := by
  have h := checkLog_sound (w := (2537 / 7703)) (n := 12)
    (lo := (171050731 / 250000000)) (hi := (27368117 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2583) = 1/(2583 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-27368117 / 40000000) (-171050731 / 250000000) (Real.log (2583 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (402073947 / 1000000000) ≤ -Real.log (2560 / 3827) ∧
    -Real.log (2560 / 3827) ≤ (100518487 / 250000000) := by
  have h := checkLog_sound (w := (1267 / 6387)) (n := 12)
    (lo := (402073947 / 1000000000)) (hi := (100518487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3827 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3827 / 2560) = 1/(2560 / 3827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (402073947 / 1000000000) (100518487 / 250000000) (Real.log (3827 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3827 / 2560) = -Real.log (2560 / 3827) := by
    rw [show ((3827 / 2560) : ℝ) = ((2560 / 3827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (341521079 / 500000000) ≤ -Real.log (1293 / 2560) ∧
    -Real.log (1293 / 2560) ≤ (683042159 / 1000000000) := by
  have h := checkLog_sound (w := (1267 / 3853)) (n := 12)
    (lo := (341521079 / 500000000)) (hi := (683042159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1293) = 1/(1293 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-683042159 / 1000000000) (-341521079 / 500000000) (Real.log (1293 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (303028461 / 1000000000) ≤ -Real.log (1000000 / 1353953) ∧
    -Real.log (1000000 / 1353953) ≤ (151514231 / 500000000) := by
  have h := checkLog_sound (w := (353953 / 2353953)) (n := 12)
    (lo := (303028461 / 1000000000)) (hi := (151514231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353953 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1353953 / 1000000) = 1/(1000000 / 1353953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (303028461 / 1000000000) (151514231 / 500000000) (Real.log (1353953 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1353953 / 1000000) = -Real.log (1000000 / 1353953) := by
    rw [show ((1353953 / 1000000) : ℝ) = ((1000000 / 1353953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (218441511 / 500000000) ≤ -Real.log (646047 / 1000000) ∧
    -Real.log (646047 / 1000000) ≤ (436883023 / 1000000000) := by
  have h := checkLog_sound (w := (353953 / 1646047)) (n := 12)
    (lo := (218441511 / 500000000)) (hi := (436883023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 646047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 646047) = 1/(646047 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-436883023 / 1000000000) (-218441511 / 500000000) (Real.log (646047 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (151673369 / 500000000) ≤ -Real.log (62500 / 84649) ∧
    -Real.log (62500 / 84649) ≤ (303346739 / 1000000000) := by
  have h := checkLog_sound (w := (22149 / 147149)) (n := 12)
    (lo := (151673369 / 500000000)) (hi := (303346739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84649 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84649 / 62500) = 1/(62500 / 84649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (151673369 / 500000000) (303346739 / 1000000000) (Real.log (84649 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (84649 / 62500) = -Real.log (62500 / 84649) := by
    rw [show ((84649 / 62500) : ℝ) = ((62500 / 84649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (437550379 / 1000000000) ≤ -Real.log (40351 / 62500) ∧
    -Real.log (40351 / 62500) ≤ (21877519 / 50000000) := by
  have h := checkLog_sound (w := (22149 / 102851)) (n := 12)
    (lo := (437550379 / 1000000000)) (hi := (21877519 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 40351) = 1/(40351 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-21877519 / 50000000) (-437550379 / 1000000000) (Real.log (40351 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (230531393 / 1000000000) ≤ -Real.log (1000000 / 1259269) ∧
    -Real.log (1000000 / 1259269) ≤ (115265697 / 500000000) := by
  have h := checkLog_sound (w := (259269 / 2259269)) (n := 12)
    (lo := (230531393 / 1000000000)) (hi := (115265697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259269 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259269 / 1000000) = 1/(1000000 / 1259269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (230531393 / 1000000000) (115265697 / 500000000) (Real.log (1259269 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1259269 / 1000000) = -Real.log (1000000 / 1259269) := by
    rw [show ((1259269 / 1000000) : ℝ) = ((1000000 / 1259269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (150058871 / 500000000) ≤ -Real.log (740731 / 1000000) ∧
    -Real.log (740731 / 1000000) ≤ (300117743 / 1000000000) := by
  have h := checkLog_sound (w := (259269 / 1740731)) (n := 12)
    (lo := (150058871 / 500000000)) (hi := (300117743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 740731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 740731) = 1/(740731 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-300117743 / 1000000000) (-150058871 / 500000000) (Real.log (740731 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (230800561 / 1000000000) ≤ -Real.log (125000 / 157451) ∧
    -Real.log (125000 / 157451) ≤ (115400281 / 500000000) := by
  have h := checkLog_sound (w := (32451 / 282451)) (n := 12)
    (lo := (230800561 / 1000000000)) (hi := (115400281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157451 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157451 / 125000) = 1/(125000 / 157451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (230800561 / 1000000000) (115400281 / 500000000) (Real.log (157451 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (157451 / 125000) = -Real.log (125000 / 157451) := by
    rw [show ((157451 / 125000) : ℝ) = ((125000 / 157451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (300575503 / 1000000000) ≤ -Real.log (92549 / 125000) ∧
    -Real.log (92549 / 125000) ≤ (18785969 / 62500000) := by
  have h := checkLog_sound (w := (32451 / 217549)) (n := 12)
    (lo := (300575503 / 1000000000)) (hi := (18785969 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 92549) = 1/(92549 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-18785969 / 62500000) (-300575503 / 1000000000) (Real.log (92549 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (739911483 / 1000000000) ≤ -Real.log (250000000000 / 523937499903) ∧
    -Real.log (250000000000 / 523937499903) ≤ (147982297 / 200000000) := by
  have h := checkLog_sound (w := (23937499903 / 1023937499903)) (n := 12)
    (lo := (46764303 / 1000000000)) (hi := (2922769 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((523937499903 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(523937499903 / 500000000000) = 1/(250000000000 / 523937499903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (739911483 / 1000000000) (147982297 / 200000000) (Real.log (523937499903 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (523937499903 / 250000000000) = -Real.log (250000000000 / 523937499903) := by
    rw [show ((523937499903 / 250000000000) : ℝ) = ((250000000000 / 523937499903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (740897117 / 1000000000) ≤ -Real.log (50000000000 / 104890832941) ∧
    -Real.log (50000000000 / 104890832941) ≤ (740897119 / 1000000000) := by
  have h := checkLog_sound (w := (4890832941 / 204890832941)) (n := 12)
    (lo := (47749937 / 1000000000)) (hi := (23874969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104890832941 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(104890832941 / 100000000000) = 1/(50000000000 / 104890832941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (740897117 / 1000000000) (740897119 / 1000000000) (Real.log (104890832941 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (104890832941 / 50000000000) = -Real.log (50000000000 / 104890832941) := by
    rw [show ((104890832941 / 50000000000) : ℝ) = ((50000000000 / 104890832941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (33165571 / 62500000) ≤ -Real.log (500000000000 / 850017752733) ∧
    -Real.log (500000000000 / 850017752733) ≤ (530649137 / 1000000000) := by
  have h := checkLog_sound (w := (350017752733 / 1350017752733)) (n := 12)
    (lo := (33165571 / 62500000)) (hi := (530649137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850017752733 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850017752733 / 500000000000) = 1/(500000000000 / 850017752733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (33165571 / 62500000) (530649137 / 1000000000) (Real.log (850017752733 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (850017752733 / 500000000000) = -Real.log (500000000000 / 850017752733) := by
    rw [show ((850017752733 / 500000000000) : ℝ) = ((500000000000 / 850017752733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (8302751 / 15625000) ≤ -Real.log (500000000000 / 850635879373) ∧
    -Real.log (500000000000 / 850635879373) ≤ (106275213 / 200000000) := by
  have h := checkLog_sound (w := (350635879373 / 1350635879373)) (n := 12)
    (lo := (8302751 / 15625000)) (hi := (106275213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850635879373 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850635879373 / 500000000000) = 1/(500000000000 / 850635879373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (8302751 / 15625000) (106275213 / 200000000) (Real.log (850635879373 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (850635879373 / 500000000000) = -Real.log (500000000000 / 850635879373) := by
    rw [show ((850635879373 / 500000000000) : ℝ) = ((500000000000 / 850635879373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0311
