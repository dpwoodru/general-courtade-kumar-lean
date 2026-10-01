import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0451
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

theorem reflection_log_1_neg : (46980271 / 250000000) ≤ -Real.log (10240 / 12357) ∧
    -Real.log (10240 / 12357) ≤ (37584217 / 200000000) := by
  have h := checkLog_sound (w := (2117 / 22597)) (n := 12)
    (lo := (46980271 / 250000000)) (hi := (37584217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12357 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12357 / 10240) = 1/(10240 / 12357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (46980271 / 250000000) (37584217 / 200000000) (Real.log (12357 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12357 / 10240) = -Real.log (10240 / 12357) := by
    rw [show ((12357 / 10240) : ℝ) = ((10240 / 12357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (9264083 / 40000000) ≤ -Real.log (8123 / 10240) ∧
    -Real.log (8123 / 10240) ≤ (57900519 / 250000000) := by
  have h := checkLog_sound (w := (2117 / 18363)) (n := 12)
    (lo := (9264083 / 40000000)) (hi := (57900519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8123) = 1/(8123 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-57900519 / 250000000) (-9264083 / 40000000) (Real.log (8123 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (187678277 / 1000000000) ≤ -Real.log (5120 / 6177) ∧
    -Real.log (5120 / 6177) ≤ (93839139 / 500000000) := by
  have h := checkLog_sound (w := (1057 / 11297)) (n := 12)
    (lo := (187678277 / 1000000000)) (hi := (93839139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6177 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6177 / 5120) = 1/(5120 / 6177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (187678277 / 1000000000) (93839139 / 500000000) (Real.log (6177 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6177 / 5120) = -Real.log (5120 / 6177) := by
    rw [show ((6177 / 5120) : ℝ) = ((5120 / 6177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (115616411 / 500000000) ≤ -Real.log (4063 / 5120) ∧
    -Real.log (4063 / 5120) ≤ (231232823 / 1000000000) := by
  have h := checkLog_sound (w := (1057 / 9183)) (n := 12)
    (lo := (115616411 / 500000000)) (hi := (231232823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4063) = 1/(4063 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-231232823 / 1000000000) (-115616411 / 500000000) (Real.log (4063 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (86513079 / 250000000) ≤ -Real.log (5120 / 7237) ∧
    -Real.log (5120 / 7237) ≤ (346052317 / 1000000000) := by
  have h := checkLog_sound (w := (2117 / 12357)) (n := 12)
    (lo := (86513079 / 250000000)) (hi := (346052317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7237 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7237 / 5120) = 1/(5120 / 7237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (86513079 / 250000000) (346052317 / 1000000000) (Real.log (7237 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7237 / 5120) = -Real.log (5120 / 7237) := by
    rw [show ((7237 / 5120) : ℝ) = ((5120 / 7237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (10670853 / 20000000) ≤ -Real.log (3003 / 5120) ∧
    -Real.log (3003 / 5120) ≤ (533542651 / 1000000000) := by
  have h := checkLog_sound (w := (2117 / 8123)) (n := 12)
    (lo := (10670853 / 20000000)) (hi := (533542651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3003) = 1/(3003 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-533542651 / 1000000000) (-10670853 / 20000000) (Real.log (3003 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (172818847 / 500000000) ≤ -Real.log (2560 / 3617) ∧
    -Real.log (2560 / 3617) ≤ (69127539 / 200000000) := by
  have h := checkLog_sound (w := (1057 / 6177)) (n := 12)
    (lo := (172818847 / 500000000)) (hi := (69127539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3617 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3617 / 2560) = 1/(2560 / 3617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (172818847 / 500000000) (69127539 / 200000000) (Real.log (3617 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3617 / 2560) = -Real.log (2560 / 3617) := by
    rw [show ((3617 / 2560) : ℝ) = ((2560 / 3617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (532544147 / 1000000000) ≤ -Real.log (1503 / 2560) ∧
    -Real.log (1503 / 2560) ≤ (133136037 / 250000000) := by
  have h := checkLog_sound (w := (1057 / 4063)) (n := 12)
    (lo := (532544147 / 1000000000)) (hi := (133136037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1503) = 1/(1503 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-133136037 / 250000000) (-532544147 / 1000000000) (Real.log (1503 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (128943281 / 500000000) ≤ -Real.log (62500 / 80887) ∧
    -Real.log (62500 / 80887) ≤ (257886563 / 1000000000) := by
  have h := checkLog_sound (w := (18387 / 143387)) (n := 12)
    (lo := (128943281 / 500000000)) (hi := (257886563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80887 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80887 / 62500) = 1/(62500 / 80887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (128943281 / 500000000) (257886563 / 1000000000) (Real.log (80887 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (80887 / 62500) = -Real.log (62500 / 80887) := by
    rw [show ((80887 / 62500) : ℝ) = ((62500 / 80887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (348412033 / 1000000000) ≤ -Real.log (44113 / 62500) ∧
    -Real.log (44113 / 62500) ≤ (174206017 / 500000000) := by
  have h := checkLog_sound (w := (18387 / 106613)) (n := 12)
    (lo := (348412033 / 1000000000)) (hi := (174206017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44113) = 1/(44113 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-174206017 / 500000000) (-348412033 / 1000000000) (Real.log (44113 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (25821567 / 100000000) ≤ -Real.log (500000 / 647309) ∧
    -Real.log (500000 / 647309) ≤ (258215671 / 1000000000) := by
  have h := checkLog_sound (w := (147309 / 1147309)) (n := 12)
    (lo := (25821567 / 100000000)) (hi := (258215671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647309 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647309 / 500000) = 1/(500000 / 647309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (25821567 / 100000000) (258215671 / 1000000000) (Real.log (647309 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (647309 / 500000) = -Real.log (500000 / 647309) := by
    rw [show ((647309 / 500000) : ℝ) = ((500000 / 647309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (174507889 / 500000000) ≤ -Real.log (352691 / 500000) ∧
    -Real.log (352691 / 500000) ≤ (349015779 / 1000000000) := by
  have h := checkLog_sound (w := (147309 / 852691)) (n := 12)
    (lo := (174507889 / 500000000)) (hi := (349015779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 352691) = 1/(352691 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-349015779 / 1000000000) (-174507889 / 500000000) (Real.log (352691 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (193206269 / 1000000000) ≤ -Real.log (1000000 / 1213133) ∧
    -Real.log (1000000 / 1213133) ≤ (19320627 / 100000000) := by
  have h := checkLog_sound (w := (213133 / 2213133)) (n := 12)
    (lo := (193206269 / 1000000000)) (hi := (19320627 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213133 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1213133 / 1000000) = 1/(1000000 / 1213133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (193206269 / 1000000000) (19320627 / 100000000) (Real.log (1213133 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1213133 / 1000000) = -Real.log (1000000 / 1213133) := by
    rw [show ((1213133 / 1000000) : ℝ) = ((1000000 / 1213133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (239696041 / 1000000000) ≤ -Real.log (786867 / 1000000) ∧
    -Real.log (786867 / 1000000) ≤ (119848021 / 500000000) := by
  have h := checkLog_sound (w := (213133 / 1786867)) (n := 12)
    (lo := (239696041 / 1000000000)) (hi := (119848021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 786867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 786867) = 1/(786867 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-119848021 / 500000000) (-239696041 / 1000000000) (Real.log (786867 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (19347331 / 100000000) ≤ -Real.log (1000000 / 1213457) ∧
    -Real.log (1000000 / 1213457) ≤ (193473311 / 1000000000) := by
  have h := checkLog_sound (w := (213457 / 2213457)) (n := 12)
    (lo := (19347331 / 100000000)) (hi := (193473311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1213457 / 1000000) = 1/(1000000 / 1213457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19347331 / 100000000) (193473311 / 1000000000) (Real.log (1213457 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1213457 / 1000000) = -Real.log (1000000 / 1213457) := by
    rw [show ((1213457 / 1000000) : ℝ) = ((1000000 / 1213457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (48021577 / 200000000) ≤ -Real.log (786543 / 1000000) ∧
    -Real.log (786543 / 1000000) ≤ (120053943 / 500000000) := by
  have h := checkLog_sound (w := (213457 / 1786543)) (n := 12)
    (lo := (48021577 / 200000000)) (hi := (120053943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 786543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 786543) = 1/(786543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-120053943 / 500000000) (-48021577 / 200000000) (Real.log (786543 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (121259719 / 200000000) ≤ -Real.log (15625000000 / 28650497019) ∧
    -Real.log (15625000000 / 28650497019) ≤ (151574649 / 250000000) := by
  have h := checkLog_sound (w := (13025497019 / 44275497019)) (n := 12)
    (lo := (121259719 / 200000000)) (hi := (151574649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28650497019 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28650497019 / 15625000000) = 1/(15625000000 / 28650497019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (121259719 / 200000000) (151574649 / 250000000) (Real.log (28650497019 / 15625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (28650497019 / 15625000000) = -Real.log (15625000000 / 28650497019) := by
    rw [show ((28650497019 / 15625000000) : ℝ) = ((15625000000 / 28650497019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (607231449 / 1000000000) ≤ -Real.log (125000000000 / 229417889881) ∧
    -Real.log (125000000000 / 229417889881) ≤ (12144629 / 20000000) := by
  have h := checkLog_sound (w := (104417889881 / 354417889881)) (n := 12)
    (lo := (607231449 / 1000000000)) (hi := (12144629 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229417889881 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229417889881 / 125000000000) = 1/(125000000000 / 229417889881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (607231449 / 1000000000) (12144629 / 20000000) (Real.log (229417889881 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (229417889881 / 125000000000) = -Real.log (125000000000 / 229417889881) := by
    rw [show ((229417889881 / 125000000000) : ℝ) = ((125000000000 / 229417889881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (43290231 / 100000000) ≤ -Real.log (62500000000 / 96357850183) ∧
    -Real.log (62500000000 / 96357850183) ≤ (432902311 / 1000000000) := by
  have h := checkLog_sound (w := (33857850183 / 158857850183)) (n := 12)
    (lo := (43290231 / 100000000)) (hi := (432902311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96357850183 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96357850183 / 62500000000) = 1/(62500000000 / 96357850183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (43290231 / 100000000) (432902311 / 1000000000) (Real.log (96357850183 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (96357850183 / 62500000000) = -Real.log (62500000000 / 96357850183) := by
    rw [show ((96357850183 / 62500000000) : ℝ) = ((62500000000 / 96357850183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (108395299 / 250000000) ≤ -Real.log (125000000000 / 192846576729) ∧
    -Real.log (125000000000 / 192846576729) ≤ (433581197 / 1000000000) := by
  have h := checkLog_sound (w := (67846576729 / 317846576729)) (n := 12)
    (lo := (108395299 / 250000000)) (hi := (433581197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192846576729 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192846576729 / 125000000000) = 1/(125000000000 / 192846576729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (108395299 / 250000000) (433581197 / 1000000000) (Real.log (192846576729 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (192846576729 / 125000000000) = -Real.log (125000000000 / 192846576729) := by
    rw [show ((192846576729 / 125000000000) : ℝ) = ((125000000000 / 192846576729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0451
