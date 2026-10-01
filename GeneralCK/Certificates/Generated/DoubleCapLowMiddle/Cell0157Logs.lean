import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0157
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

theorem reflection_log_1_neg : (324001353 / 500000000) ≤ -Real.log (1280 / 2447) ∧
    -Real.log (1280 / 2447) ≤ (648002707 / 1000000000) := by
  have h := checkLog_sound (w := (1167 / 3727)) (n := 12)
    (lo := (324001353 / 500000000)) (hi := (648002707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2447 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2447 / 1280) = 1/(1280 / 2447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (324001353 / 500000000) (648002707 / 1000000000) (Real.log (2447 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2447 / 1280) = -Real.log (1280 / 2447) := by
    rw [show ((2447 / 1280) : ℝ) = ((1280 / 2447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (151701721 / 62500000) ≤ -Real.log (113 / 1280) ∧
    -Real.log (113 / 1280) ≤ (121361377 / 50000000) := by
  have h := checkLog_sound (w := (47 / 273)) (n := 12)
    (lo := (86946499 / 250000000)) (hi := (347785997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 113) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 113) = 1/(113 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-121361377 / 50000000) (-151701721 / 62500000) (Real.log (113 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (647225943 / 1000000000) ≤ -Real.log (12800 / 24451) ∧
    -Real.log (12800 / 24451) ≤ (80903243 / 125000000) := by
  have h := checkLog_sound (w := (11651 / 37251)) (n := 12)
    (lo := (647225943 / 1000000000)) (hi := (80903243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24451 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24451 / 12800) = 1/(12800 / 24451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (647225943 / 1000000000) (80903243 / 125000000) (Real.log (24451 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24451 / 12800) = -Real.log (12800 / 24451) := by
    rw [show ((24451 / 12800) : ℝ) = ((12800 / 24451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (241055317 / 100000000) ≤ -Real.log (1149 / 12800) ∧
    -Real.log (1149 / 12800) ≤ (1205276587 / 500000000) := by
  have h := checkLog_sound (w := (451 / 2749)) (n := 12)
    (lo := (33111163 / 100000000)) (hi := (331111631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1149) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1149) = 1/(1149 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1205276587 / 500000000) (-241055317 / 100000000) (Real.log (1149 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (120144691 / 200000000) ≤ -Real.log (640 / 1167) ∧
    -Real.log (640 / 1167) ≤ (1173288 / 1953125) := by
  have h := checkLog_sound (w := (527 / 1807)) (n := 12)
    (lo := (120144691 / 200000000)) (hi := (1173288 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1167 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1167 / 640) = 1/(640 / 1167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (120144691 / 200000000) (1173288 / 1953125) (Real.log (1167 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1167 / 640) = -Real.log (640 / 1167) := by
    rw [show ((1167 / 640) : ℝ) = ((640 / 1167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (433520089 / 250000000) ≤ -Real.log (113 / 640) ∧
    -Real.log (113 / 640) ≤ (1734080359 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 273)) (n := 12)
    (lo := (86946499 / 250000000)) (hi := (347785997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 113) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 113) = 1/(113 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1734080359 / 1000000000) (-433520089 / 250000000) (Real.log (113 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (299547011 / 500000000) ≤ -Real.log (6400 / 11651) ∧
    -Real.log (6400 / 11651) ≤ (599094023 / 1000000000) := by
  have h := checkLog_sound (w := (5251 / 18051)) (n := 12)
    (lo := (299547011 / 500000000)) (hi := (599094023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11651 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11651 / 6400) = 1/(6400 / 11651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (299547011 / 500000000) (599094023 / 1000000000) (Real.log (11651 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11651 / 6400) = -Real.log (6400 / 11651) := by
    rw [show ((11651 / 6400) : ℝ) = ((6400 / 11651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (171740599 / 100000000) ≤ -Real.log (1149 / 6400) ∧
    -Real.log (1149 / 6400) ≤ (1717405993 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 2749)) (n := 12)
    (lo := (33111163 / 100000000)) (hi := (331111631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1149) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1149) = 1/(1149 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1717405993 / 1000000000) (-171740599 / 100000000) (Real.log (1149 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (328871647 / 500000000) ≤ -Real.log (1000000 / 1930431) ∧
    -Real.log (1000000 / 1930431) ≤ (131548659 / 200000000) := by
  have h := checkLog_sound (w := (930431 / 2930431)) (n := 12)
    (lo := (328871647 / 500000000)) (hi := (131548659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1930431 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1930431 / 1000000) = 1/(1000000 / 1930431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (328871647 / 500000000) (131548659 / 200000000) (Real.log (1930431 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1930431 / 1000000) = -Real.log (1000000 / 1930431) := by
    rw [show ((1930431 / 1000000) : ℝ) = ((1000000 / 1930431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2665436211 / 1000000000) ≤ -Real.log (69569 / 1000000) ∧
    -Real.log (69569 / 1000000) ≤ (533087243 / 200000000) := by
  have h := checkLog_sound (w := (55431 / 194569)) (n := 12)
    (lo := (585994671 / 1000000000)) (hi := (36624667 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 69569) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 69569) = 1/(69569 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-533087243 / 200000000) (-2665436211 / 1000000000) (Real.log (69569 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (658280853 / 1000000000) ≤ -Real.log (1000000 / 1931469) ∧
    -Real.log (1000000 / 1931469) ≤ (329140427 / 500000000) := by
  have h := checkLog_sound (w := (931469 / 2931469)) (n := 12)
    (lo := (658280853 / 1000000000)) (hi := (329140427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1931469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1931469 / 1000000) = 1/(1000000 / 1931469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (658280853 / 1000000000) (329140427 / 500000000) (Real.log (1931469 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1931469 / 1000000) = -Real.log (1000000 / 1931469) := by
    rw [show ((1931469 / 1000000) : ℝ) = ((1000000 / 1931469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2680469079 / 1000000000) ≤ -Real.log (68531 / 1000000) ∧
    -Real.log (68531 / 1000000) ≤ (2680469083 / 1000000000) := by
  have h := checkLog_sound (w := (56469 / 193531)) (n := 12)
    (lo := (601027539 / 1000000000)) (hi := (30051377 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 68531) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 68531) = 1/(68531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2680469083 / 1000000000) (-2680469079 / 1000000000) (Real.log (68531 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (164197421 / 250000000) ≤ -Real.log (1000000 / 1928591) ∧
    -Real.log (1000000 / 1928591) ≤ (131357937 / 200000000) := by
  have h := checkLog_sound (w := (928591 / 2928591)) (n := 12)
    (lo := (164197421 / 250000000)) (hi := (131357937 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1928591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1928591 / 1000000) = 1/(1000000 / 1928591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (164197421 / 250000000) (131357937 / 200000000) (Real.log (1928591 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1928591 / 1000000) = -Real.log (1000000 / 1928591) := by
    rw [show ((1928591 / 1000000) : ℝ) = ((1000000 / 1928591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (527866273 / 200000000) ≤ -Real.log (71409 / 1000000) ∧
    -Real.log (71409 / 1000000) ≤ (2639331369 / 1000000000) := by
  have h := checkLog_sound (w := (53591 / 196409)) (n := 12)
    (lo := (22395593 / 40000000)) (hi := (279944913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 71409) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 71409) = 1/(71409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2639331369 / 1000000000) (-527866273 / 200000000) (Real.log (71409 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (657363513 / 1000000000) ≤ -Real.log (500000 / 964849) ∧
    -Real.log (500000 / 964849) ≤ (328681757 / 500000000) := by
  have h := checkLog_sound (w := (464849 / 1464849)) (n := 12)
    (lo := (657363513 / 1000000000)) (hi := (328681757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((964849 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(964849 / 500000) = 1/(500000 / 964849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (657363513 / 1000000000) (328681757 / 500000000) (Real.log (964849 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (964849 / 500000) = -Real.log (500000 / 964849) := by
    rw [show ((964849 / 500000) : ℝ) = ((500000 / 964849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2654955029 / 1000000000) ≤ -Real.log (35151 / 500000) ∧
    -Real.log (35151 / 500000) ≤ (2654955033 / 1000000000) := by
  have h := checkLog_sound (w := (27349 / 97651)) (n := 12)
    (lo := (575513489 / 1000000000)) (hi := (57551349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35151) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 35151) = 1/(35151 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2654955033 / 1000000000) (-2654955029 / 1000000000) (Real.log (35151 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (207698719 / 62500000) ≤ -Real.log (250000000000 / 6937109200937) ∧
    -Real.log (250000000000 / 6937109200937) ≤ (3323179509 / 1000000000) := by
  have h := checkLog_sound (w := (2937109200937 / 10937109200937)) (n := 12)
    (lo := (8602981 / 15625000)) (hi := (110118157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6937109200937 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6937109200937 / 4000000000000) = 1/(250000000000 / 6937109200937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (207698719 / 62500000) (3323179509 / 1000000000) (Real.log (6937109200937 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6937109200937 / 250000000000) = -Real.log (250000000000 / 6937109200937) := by
    rw [show ((6937109200937 / 250000000000) : ℝ) = ((250000000000 / 6937109200937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (834687483 / 250000000) ≤ -Real.log (500000000000 / 14091936495893) ∧
    -Real.log (500000000000 / 14091936495893) ≤ (3338749937 / 1000000000) := by
  have h := checkLog_sound (w := (6091936495893 / 22091936495893)) (n := 12)
    (lo := (141540303 / 250000000)) (hi := (566161213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14091936495893 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(14091936495893 / 8000000000000) = 1/(500000000000 / 14091936495893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (834687483 / 250000000) (3338749937 / 1000000000) (Real.log (14091936495893 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14091936495893 / 500000000000) = -Real.log (500000000000 / 14091936495893) := by
    rw [show ((14091936495893 / 500000000000) : ℝ) = ((500000000000 / 14091936495893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3296121049 / 1000000000) ≤ -Real.log (62500000000 / 1687979631419) ∧
    -Real.log (62500000000 / 1687979631419) ≤ (1648060527 / 500000000) := by
  have h := checkLog_sound (w := (687979631419 / 2687979631419)) (n := 12)
    (lo := (523532329 / 1000000000)) (hi := (52353233 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1687979631419 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1687979631419 / 1000000000000) = 1/(62500000000 / 1687979631419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3296121049 / 1000000000) (1648060527 / 500000000) (Real.log (1687979631419 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1687979631419 / 62500000000) = -Real.log (62500000000 / 1687979631419) := by
    rw [show ((1687979631419 / 62500000000) : ℝ) = ((62500000000 / 1687979631419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1656159271 / 500000000) ≤ -Real.log (125000000000 / 3431086597821) ∧
    -Real.log (125000000000 / 3431086597821) ≤ (3312318547 / 1000000000) := by
  have h := checkLog_sound (w := (1431086597821 / 5431086597821)) (n := 12)
    (lo := (269864911 / 500000000)) (hi := (539729823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3431086597821 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3431086597821 / 2000000000000) = 1/(125000000000 / 3431086597821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1656159271 / 500000000) (3312318547 / 1000000000) (Real.log (3431086597821 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3431086597821 / 125000000000) = -Real.log (125000000000 / 3431086597821) := by
    rw [show ((3431086597821 / 125000000000) : ℝ) = ((125000000000 / 3431086597821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0157
