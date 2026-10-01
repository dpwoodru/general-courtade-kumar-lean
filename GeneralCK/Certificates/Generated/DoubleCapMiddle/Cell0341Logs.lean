import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0341
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

theorem reflection_log_1_neg : (214276227 / 1000000000) ≤ -Real.log (10240 / 12687) ∧
    -Real.log (10240 / 12687) ≤ (53569057 / 250000000) := by
  have h := checkLog_sound (w := (2447 / 22927)) (n := 12)
    (lo := (214276227 / 1000000000)) (hi := (53569057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12687 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12687 / 10240) = 1/(10240 / 12687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (214276227 / 1000000000) (53569057 / 250000000) (Real.log (12687 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12687 / 10240) = -Real.log (10240 / 12687) := by
    rw [show ((12687 / 10240) : ℝ) = ((10240 / 12687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (68268931 / 250000000) ≤ -Real.log (7793 / 10240) ∧
    -Real.log (7793 / 10240) ≤ (10923029 / 40000000) := by
  have h := checkLog_sound (w := (2447 / 18033)) (n := 12)
    (lo := (68268931 / 250000000)) (hi := (10923029 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7793) = 1/(7793 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-10923029 / 40000000) (-68268931 / 250000000) (Real.log (7793 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (214039737 / 1000000000) ≤ -Real.log (2560 / 3171) ∧
    -Real.log (2560 / 3171) ≤ (107019869 / 500000000) := by
  have h := checkLog_sound (w := (611 / 5731)) (n := 12)
    (lo := (214039737 / 1000000000)) (hi := (107019869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3171 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3171 / 2560) = 1/(2560 / 3171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (214039737 / 1000000000) (107019869 / 500000000) (Real.log (3171 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3171 / 2560) = -Real.log (2560 / 3171) := by
    rw [show ((3171 / 2560) : ℝ) = ((2560 / 3171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (272690837 / 1000000000) ≤ -Real.log (1949 / 2560) ∧
    -Real.log (1949 / 2560) ≤ (136345419 / 500000000) := by
  have h := checkLog_sound (w := (611 / 4509)) (n := 12)
    (lo := (272690837 / 1000000000)) (hi := (136345419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1949) = 1/(1949 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-136345419 / 500000000) (-272690837 / 1000000000) (Real.log (1949 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (48830281 / 125000000) ≤ -Real.log (5120 / 7567) ∧
    -Real.log (5120 / 7567) ≤ (390642249 / 1000000000) := by
  have h := checkLog_sound (w := (2447 / 12687)) (n := 12)
    (lo := (48830281 / 125000000)) (hi := (390642249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7567 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7567 / 5120) = 1/(5120 / 7567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (48830281 / 125000000) (390642249 / 1000000000) (Real.log (7567 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7567 / 5120) = -Real.log (5120 / 7567) := by
    rw [show ((7567 / 5120) : ℝ) = ((5120 / 7567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (649953001 / 1000000000) ≤ -Real.log (2673 / 5120) ∧
    -Real.log (2673 / 5120) ≤ (324976501 / 500000000) := by
  have h := checkLog_sound (w := (2447 / 7793)) (n := 12)
    (lo := (649953001 / 1000000000)) (hi := (324976501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2673) = 1/(2673 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-324976501 / 500000000) (-649953001 / 1000000000) (Real.log (2673 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (390245711 / 1000000000) ≤ -Real.log (1280 / 1891) ∧
    -Real.log (1280 / 1891) ≤ (24390357 / 62500000) := by
  have h := checkLog_sound (w := (611 / 3171)) (n := 12)
    (lo := (390245711 / 1000000000)) (hi := (24390357 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1891 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1891 / 1280) = 1/(1280 / 1891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (390245711 / 1000000000) (24390357 / 62500000) (Real.log (1891 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1891 / 1280) = -Real.log (1280 / 1891) := by
    rw [show ((1891 / 1280) : ℝ) = ((1280 / 1891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (10137989 / 15625000) ≤ -Real.log (669 / 1280) ∧
    -Real.log (669 / 1280) ≤ (648831297 / 1000000000) := by
  have h := checkLog_sound (w := (611 / 1949)) (n := 12)
    (lo := (10137989 / 15625000)) (hi := (648831297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 669) = 1/(669 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-648831297 / 1000000000) (-10137989 / 15625000) (Real.log (669 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (36684687 / 125000000) ≤ -Real.log (1000000 / 1341083) ∧
    -Real.log (1000000 / 1341083) ≤ (293477497 / 1000000000) := by
  have h := checkLog_sound (w := (341083 / 2341083)) (n := 12)
    (lo := (36684687 / 125000000)) (hi := (293477497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341083 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341083 / 1000000) = 1/(1000000 / 1341083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (36684687 / 125000000) (293477497 / 1000000000) (Real.log (1341083 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1341083 / 1000000) = -Real.log (1000000 / 1341083) := by
    rw [show ((1341083 / 1000000) : ℝ) = ((1000000 / 1341083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4171577 / 10000000) ≤ -Real.log (658917 / 1000000) ∧
    -Real.log (658917 / 1000000) ≤ (417157701 / 1000000000) := by
  have h := checkLog_sound (w := (341083 / 1658917)) (n := 12)
    (lo := (4171577 / 10000000)) (hi := (417157701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 658917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 658917) = 1/(658917 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-417157701 / 1000000000) (-4171577 / 10000000) (Real.log (658917 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (36724667 / 125000000) ≤ -Real.log (125000 / 167689) ∧
    -Real.log (125000 / 167689) ≤ (293797337 / 1000000000) := by
  have h := checkLog_sound (w := (42689 / 292689)) (n := 12)
    (lo := (36724667 / 125000000)) (hi := (293797337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167689 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167689 / 125000) = 1/(125000 / 167689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (36724667 / 125000000) (293797337 / 1000000000) (Real.log (167689 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (167689 / 125000) = -Real.log (125000 / 167689) := by
    rw [show ((167689 / 125000) : ℝ) = ((125000 / 167689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (417808981 / 1000000000) ≤ -Real.log (82311 / 125000) ∧
    -Real.log (82311 / 125000) ≤ (208904491 / 500000000) := by
  have h := checkLog_sound (w := (42689 / 207311)) (n := 12)
    (lo := (417808981 / 1000000000)) (hi := (208904491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 82311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 82311) = 1/(82311 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-208904491 / 500000000) (-417808981 / 1000000000) (Real.log (82311 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (55626837 / 250000000) ≤ -Real.log (200000 / 249841) ∧
    -Real.log (200000 / 249841) ≤ (222507349 / 1000000000) := by
  have h := checkLog_sound (w := (49841 / 449841)) (n := 12)
    (lo := (55626837 / 250000000)) (hi := (222507349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249841 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249841 / 200000) = 1/(200000 / 249841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (55626837 / 250000000) (222507349 / 1000000000) (Real.log (249841 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (249841 / 200000) = -Real.log (200000 / 249841) := by
    rw [show ((249841 / 200000) : ℝ) = ((200000 / 249841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (286622633 / 1000000000) ≤ -Real.log (150159 / 200000) ∧
    -Real.log (150159 / 200000) ≤ (143311317 / 500000000) := by
  have h := checkLog_sound (w := (49841 / 350159)) (n := 12)
    (lo := (286622633 / 1000000000)) (hi := (143311317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 150159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 150159) = 1/(150159 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-143311317 / 500000000) (-286622633 / 1000000000) (Real.log (150159 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (222775483 / 1000000000) ≤ -Real.log (50000 / 62477) ∧
    -Real.log (50000 / 62477) ≤ (55693871 / 250000000) := by
  have h := checkLog_sound (w := (12477 / 112477)) (n := 12)
    (lo := (222775483 / 1000000000)) (hi := (55693871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62477 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62477 / 50000) = 1/(50000 / 62477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (222775483 / 1000000000) (55693871 / 250000000) (Real.log (62477 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (62477 / 50000) = -Real.log (50000 / 62477) := by
    rw [show ((62477 / 50000) : ℝ) = ((50000 / 62477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (287068927 / 1000000000) ≤ -Real.log (37523 / 50000) ∧
    -Real.log (37523 / 50000) ≤ (1121363 / 3906250) := by
  have h := checkLog_sound (w := (12477 / 87523)) (n := 12)
    (lo := (287068927 / 1000000000)) (hi := (1121363 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37523) = 1/(37523 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1121363 / 3906250) (-287068927 / 1000000000) (Real.log (37523 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (177658799 / 250000000) ≤ -Real.log (250000000000 / 508820913711) ∧
    -Real.log (250000000000 / 508820913711) ≤ (355317599 / 500000000) := by
  have h := checkLog_sound (w := (8820913711 / 1008820913711)) (n := 12)
    (lo := (1093001 / 62500000)) (hi := (17488017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((508820913711 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(508820913711 / 500000000000) = 1/(250000000000 / 508820913711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (177658799 / 250000000) (355317599 / 500000000) (Real.log (508820913711 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (508820913711 / 250000000000) = -Real.log (250000000000 / 508820913711) := by
    rw [show ((508820913711 / 250000000000) : ℝ) = ((250000000000 / 508820913711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (177901579 / 250000000) ≤ -Real.log (500000000000 / 1018630559707) ∧
    -Real.log (500000000000 / 1018630559707) ≤ (355803159 / 500000000) := by
  have h := checkLog_sound (w := (18630559707 / 2018630559707)) (n := 12)
    (lo := (36053 / 1953125)) (hi := (18459137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1018630559707 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1018630559707 / 1000000000000) = 1/(500000000000 / 1018630559707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (177901579 / 250000000) (355803159 / 500000000) (Real.log (1018630559707 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1018630559707 / 500000000000) = -Real.log (500000000000 / 1018630559707) := by
    rw [show ((1018630559707 / 500000000000) : ℝ) = ((500000000000 / 1018630559707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (254564991 / 500000000) ≤ -Real.log (250000000000 / 415960748273) ∧
    -Real.log (250000000000 / 415960748273) ≤ (509129983 / 1000000000) := by
  have h := checkLog_sound (w := (165960748273 / 665960748273)) (n := 12)
    (lo := (254564991 / 500000000)) (hi := (509129983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((415960748273 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(415960748273 / 250000000000) = 1/(250000000000 / 415960748273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (254564991 / 500000000) (509129983 / 1000000000) (Real.log (415960748273 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (415960748273 / 250000000000) = -Real.log (250000000000 / 415960748273) := by
    rw [show ((415960748273 / 250000000000) : ℝ) = ((250000000000 / 415960748273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (50984441 / 100000000) ≤ -Real.log (500000000000 / 832516056819) ∧
    -Real.log (500000000000 / 832516056819) ≤ (509844411 / 1000000000) := by
  have h := checkLog_sound (w := (332516056819 / 1332516056819)) (n := 12)
    (lo := (50984441 / 100000000)) (hi := (509844411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((832516056819 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(832516056819 / 500000000000) = 1/(500000000000 / 832516056819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (50984441 / 100000000) (509844411 / 1000000000) (Real.log (832516056819 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (832516056819 / 500000000000) = -Real.log (500000000000 / 832516056819) := by
    rw [show ((832516056819 / 500000000000) : ℝ) = ((500000000000 / 832516056819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0341
