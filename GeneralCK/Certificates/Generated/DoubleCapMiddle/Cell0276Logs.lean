import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0276
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

theorem reflection_log_1_neg : (230925691 / 1000000000) ≤ -Real.log (512 / 645) ∧
    -Real.log (512 / 645) ≤ (57731423 / 250000000) := by
  have h := checkLog_sound (w := (133 / 1157)) (n := 12)
    (lo := (230925691 / 1000000000)) (hi := (57731423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((645 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(645 / 512) = 1/(512 / 645) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (230925691 / 1000000000) (57731423 / 250000000) (Real.log (645 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (645 / 512) = -Real.log (512 / 645) := by
    rw [show ((645 / 512) : ℝ) = ((512 / 645) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (300788419 / 1000000000) ≤ -Real.log (379 / 512) ∧
    -Real.log (379 / 512) ≤ (15039421 / 50000000) := by
  have h := checkLog_sound (w := (133 / 891)) (n := 12)
    (lo := (300788419 / 1000000000)) (hi := (15039421 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 379) = 1/(379 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-15039421 / 50000000) (-300788419 / 1000000000) (Real.log (379 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (230460467 / 1000000000) ≤ -Real.log (5120 / 6447) ∧
    -Real.log (5120 / 6447) ≤ (57615117 / 250000000) := by
  have h := checkLog_sound (w := (1327 / 11567)) (n := 12)
    (lo := (230460467 / 1000000000)) (hi := (57615117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6447 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6447 / 5120) = 1/(5120 / 6447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (230460467 / 1000000000) (57615117 / 250000000) (Real.log (6447 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6447 / 5120) = -Real.log (5120 / 6447) := by
    rw [show ((6447 / 5120) : ℝ) = ((5120 / 6447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (37499647 / 125000000) ≤ -Real.log (3793 / 5120) ∧
    -Real.log (3793 / 5120) ≤ (299997177 / 1000000000) := by
  have h := checkLog_sound (w := (1327 / 8913)) (n := 12)
    (lo := (37499647 / 125000000)) (hi := (299997177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3793) = 1/(3793 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-299997177 / 1000000000) (-37499647 / 125000000) (Real.log (3793 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (418401899 / 1000000000) ≤ -Real.log (256 / 389) ∧
    -Real.log (256 / 389) ≤ (4184019 / 10000000) := by
  have h := checkLog_sound (w := (133 / 645)) (n := 12)
    (lo := (418401899 / 1000000000)) (hi := (4184019 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((389 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(389 / 256) = 1/(256 / 389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (418401899 / 1000000000) (4184019 / 10000000) (Real.log (389 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (389 / 256) = -Real.log (256 / 389) := by
    rw [show ((389 / 256) : ℝ) = ((256 / 389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (11453017 / 15625000) ≤ -Real.log (123 / 256) ∧
    -Real.log (123 / 256) ≤ (73299309 / 100000000) := by
  have h := checkLog_sound (w := (5 / 251)) (n := 12)
    (lo := (9961477 / 250000000)) (hi := (39845909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 123) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 123) = 1/(123 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-73299309 / 100000000) (-11453017 / 15625000) (Real.log (123 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (417630393 / 1000000000) ≤ -Real.log (2560 / 3887) ∧
    -Real.log (2560 / 3887) ≤ (208815197 / 500000000) := by
  have h := checkLog_sound (w := (1327 / 6447)) (n := 12)
    (lo := (417630393 / 1000000000)) (hi := (208815197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3887 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3887 / 2560) = 1/(2560 / 3887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (417630393 / 1000000000) (208815197 / 500000000) (Real.log (3887 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3887 / 2560) = -Real.log (2560 / 3887) := by
    rw [show ((3887 / 2560) : ℝ) = ((2560 / 3887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (730557033 / 1000000000) ≤ -Real.log (1233 / 2560) ∧
    -Real.log (1233 / 2560) ≤ (146111407 / 200000000) := by
  have h := checkLog_sound (w := (47 / 2513)) (n := 12)
    (lo := (37409853 / 1000000000)) (hi := (18704927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1233) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1233) = 1/(1233 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-146111407 / 200000000) (-730557033 / 1000000000) (Real.log (1233 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (78917009 / 250000000) ≤ -Real.log (40000 / 54847) ∧
    -Real.log (40000 / 54847) ≤ (315668037 / 1000000000) := by
  have h := checkLog_sound (w := (14847 / 94847)) (n := 12)
    (lo := (78917009 / 250000000)) (hi := (315668037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54847 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54847 / 40000) = 1/(40000 / 54847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (78917009 / 250000000) (315668037 / 1000000000) (Real.log (54847 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (54847 / 40000) = -Real.log (40000 / 54847) := by
    rw [show ((54847 / 40000) : ℝ) = ((40000 / 54847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (11597557 / 25000000) ≤ -Real.log (25153 / 40000) ∧
    -Real.log (25153 / 40000) ≤ (463902281 / 1000000000) := by
  have h := checkLog_sound (w := (14847 / 65153)) (n := 12)
    (lo := (11597557 / 25000000)) (hi := (463902281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 25153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 25153) = 1/(25153 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-463902281 / 1000000000) (-11597557 / 25000000) (Real.log (25153 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (316298683 / 1000000000) ≤ -Real.log (25000 / 34301) ∧
    -Real.log (25000 / 34301) ≤ (79074671 / 250000000) := by
  have h := checkLog_sound (w := (9301 / 59301)) (n := 12)
    (lo := (316298683 / 1000000000)) (hi := (79074671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34301 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34301 / 25000) = 1/(25000 / 34301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (316298683 / 1000000000) (79074671 / 250000000) (Real.log (34301 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (34301 / 25000) = -Real.log (25000 / 34301) := by
    rw [show ((34301 / 25000) : ℝ) = ((25000 / 34301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (58159851 / 125000000) ≤ -Real.log (15699 / 25000) ∧
    -Real.log (15699 / 25000) ≤ (465278809 / 1000000000) := by
  have h := checkLog_sound (w := (9301 / 40699)) (n := 12)
    (lo := (58159851 / 125000000)) (hi := (465278809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 15699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 15699) = 1/(15699 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-465278809 / 1000000000) (-58159851 / 125000000) (Real.log (15699 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (48252953 / 200000000) ≤ -Real.log (500000 / 636429) ∧
    -Real.log (500000 / 636429) ≤ (120632383 / 500000000) := by
  have h := checkLog_sound (w := (136429 / 1136429)) (n := 12)
    (lo := (48252953 / 200000000)) (hi := (120632383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636429 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636429 / 500000) = 1/(500000 / 636429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (48252953 / 200000000) (120632383 / 500000000) (Real.log (636429 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (636429 / 500000) = -Real.log (500000 / 636429) := by
    rw [show ((636429 / 500000) : ℝ) = ((500000 / 636429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (318633497 / 1000000000) ≤ -Real.log (363571 / 500000) ∧
    -Real.log (363571 / 500000) ≤ (159316749 / 500000000) := by
  have h := checkLog_sound (w := (136429 / 863571)) (n := 12)
    (lo := (318633497 / 1000000000)) (hi := (159316749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 363571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 363571) = 1/(363571 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-159316749 / 500000000) (-318633497 / 1000000000) (Real.log (363571 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (48360713 / 200000000) ≤ -Real.log (125000 / 159193) ∧
    -Real.log (125000 / 159193) ≤ (120901783 / 500000000) := by
  have h := checkLog_sound (w := (34193 / 284193)) (n := 12)
    (lo := (48360713 / 200000000)) (hi := (120901783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159193 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159193 / 125000) = 1/(125000 / 159193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (48360713 / 200000000) (120901783 / 500000000) (Real.log (159193 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (159193 / 125000) = -Real.log (125000 / 159193) := by
    rw [show ((159193 / 125000) : ℝ) = ((125000 / 159193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (159788681 / 500000000) ≤ -Real.log (90807 / 125000) ∧
    -Real.log (90807 / 125000) ≤ (319577363 / 1000000000) := by
  have h := checkLog_sound (w := (34193 / 215807)) (n := 12)
    (lo := (159788681 / 500000000)) (hi := (319577363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 90807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 90807) = 1/(90807 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-319577363 / 1000000000) (-159788681 / 500000000) (Real.log (90807 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (194892579 / 250000000) ≤ -Real.log (500000000000 / 1090267562517) ∧
    -Real.log (500000000000 / 1090267562517) ≤ (389785159 / 500000000) := by
  have h := checkLog_sound (w := (90267562517 / 2090267562517)) (n := 12)
    (lo := (2700723 / 31250000)) (hi := (86423137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090267562517 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1090267562517 / 1000000000000) = 1/(500000000000 / 1090267562517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (194892579 / 250000000) (389785159 / 500000000) (Real.log (1090267562517 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1090267562517 / 500000000000) = -Real.log (500000000000 / 1090267562517) := by
    rw [show ((1090267562517 / 500000000000) : ℝ) = ((500000000000 / 1090267562517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (781577491 / 1000000000) ≤ -Real.log (31250000000 / 68278632397) ∧
    -Real.log (31250000000 / 68278632397) ≤ (781577493 / 1000000000) := by
  have h := checkLog_sound (w := (5778632397 / 130778632397)) (n := 12)
    (lo := (88430311 / 1000000000)) (hi := (11053789 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68278632397 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(68278632397 / 62500000000) = 1/(31250000000 / 68278632397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (781577491 / 1000000000) (781577493 / 1000000000) (Real.log (68278632397 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (68278632397 / 31250000000) = -Real.log (31250000000 / 68278632397) := by
    rw [show ((68278632397 / 31250000000) : ℝ) = ((31250000000 / 68278632397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (559898263 / 1000000000) ≤ -Real.log (125000000000 / 218811800171) ∧
    -Real.log (125000000000 / 218811800171) ≤ (69987283 / 125000000) := by
  have h := checkLog_sound (w := (93811800171 / 343811800171)) (n := 12)
    (lo := (559898263 / 1000000000)) (hi := (69987283 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218811800171 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218811800171 / 125000000000) = 1/(125000000000 / 218811800171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (559898263 / 1000000000) (69987283 / 125000000) (Real.log (218811800171 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (218811800171 / 125000000000) = -Real.log (125000000000 / 218811800171) := by
    rw [show ((218811800171 / 125000000000) : ℝ) = ((125000000000 / 218811800171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (561380927 / 1000000000) ≤ -Real.log (250000000000 / 438272930501) ∧
    -Real.log (250000000000 / 438272930501) ≤ (8771577 / 15625000) := by
  have h := checkLog_sound (w := (188272930501 / 688272930501)) (n := 12)
    (lo := (561380927 / 1000000000)) (hi := (8771577 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((438272930501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(438272930501 / 250000000000) = 1/(250000000000 / 438272930501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (561380927 / 1000000000) (8771577 / 15625000) (Real.log (438272930501 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (438272930501 / 250000000000) = -Real.log (250000000000 / 438272930501) := by
    rw [show ((438272930501 / 250000000000) : ℝ) = ((250000000000 / 438272930501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0276
