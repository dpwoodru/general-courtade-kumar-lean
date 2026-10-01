import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell082
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (65328007 / 250000000) ≤ -Real.log (5120 / 6649) ∧
    -Real.log (5120 / 6649) ≤ (261312029 / 1000000000) := by
  have h := checkLog_sound (w := (1529 / 11769)) (n := 12)
    (lo := (65328007 / 250000000)) (hi := (261312029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6649 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6649 / 5120) = 1/(5120 / 6649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (65328007 / 250000000) (261312029 / 1000000000) (Real.log (6649 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6649 / 5120) = -Real.log (5120 / 6649) := by
    rw [show ((6649 / 5120) : ℝ) = ((5120 / 6649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (354723723 / 1000000000) ≤ -Real.log (3591 / 5120) ∧
    -Real.log (3591 / 5120) ≤ (88680931 / 250000000) := by
  have h := checkLog_sound (w := (1529 / 8711)) (n := 12)
    (lo := (354723723 / 1000000000)) (hi := (88680931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3591) = 1/(3591 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-88680931 / 250000000) (-354723723 / 1000000000) (Real.log (3591 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (26086073 / 100000000) ≤ -Real.log (2560 / 3323) ∧
    -Real.log (2560 / 3323) ≤ (260860731 / 1000000000) := by
  have h := checkLog_sound (w := (763 / 5883)) (n := 12)
    (lo := (26086073 / 100000000)) (hi := (260860731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3323 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3323 / 2560) = 1/(2560 / 3323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (26086073 / 100000000) (260860731 / 1000000000) (Real.log (3323 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3323 / 2560) = -Real.log (2560 / 3323) := by
    rw [show ((3323 / 2560) : ℝ) = ((2560 / 3323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (7077773 / 20000000) ≤ -Real.log (1797 / 2560) ∧
    -Real.log (1797 / 2560) ≤ (353888651 / 1000000000) := by
  have h := checkLog_sound (w := (763 / 4357)) (n := 12)
    (lo := (7077773 / 20000000)) (hi := (353888651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1797) = 1/(1797 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-353888651 / 1000000000) (-7077773 / 20000000) (Real.log (1797 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (19190961 / 100000000) ≤ -Real.log (1000000 / 1211561) ∧
    -Real.log (1000000 / 1211561) ≤ (191909611 / 1000000000) := by
  have h := checkLog_sound (w := (211561 / 2211561)) (n := 12)
    (lo := (19190961 / 100000000)) (hi := (191909611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211561 / 1000000) = 1/(1000000 / 1211561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (19190961 / 100000000) (191909611 / 1000000000) (Real.log (1211561 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1211561 / 1000000) = -Real.log (1000000 / 1211561) := by
    rw [show ((1211561 / 1000000) : ℝ) = ((1000000 / 1211561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (237700237 / 1000000000) ≤ -Real.log (788439 / 1000000) ∧
    -Real.log (788439 / 1000000) ≤ (118850119 / 500000000) := by
  have h := checkLog_sound (w := (211561 / 1788439)) (n := 12)
    (lo := (237700237 / 1000000000)) (hi := (118850119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 788439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 788439) = 1/(788439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-118850119 / 500000000) (-237700237 / 1000000000) (Real.log (788439 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (19225621 / 100000000) ≤ -Real.log (1000000 / 1211981) ∧
    -Real.log (1000000 / 1211981) ≤ (192256211 / 1000000000) := by
  have h := checkLog_sound (w := (211981 / 2211981)) (n := 12)
    (lo := (19225621 / 100000000)) (hi := (192256211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211981 / 1000000) = 1/(1000000 / 1211981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (19225621 / 100000000) (192256211 / 1000000000) (Real.log (1211981 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1211981 / 1000000) = -Real.log (1000000 / 1211981) := by
    rw [show ((1211981 / 1000000) : ℝ) = ((1000000 / 1211981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (238233077 / 1000000000) ≤ -Real.log (788019 / 1000000) ∧
    -Real.log (788019 / 1000000) ≤ (119116539 / 500000000) := by
  have h := checkLog_sound (w := (211981 / 1788019)) (n := 12)
    (lo := (238233077 / 1000000000)) (hi := (119116539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 788019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 788019) = 1/(788019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-119116539 / 500000000) (-238233077 / 1000000000) (Real.log (788019 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (141043729 / 1000000000) ≤ -Real.log (40000 / 46059) ∧
    -Real.log (40000 / 46059) ≤ (14104373 / 100000000) := by
  have h := checkLog_sound (w := (6059 / 86059)) (n := 12)
    (lo := (141043729 / 1000000000)) (hi := (14104373 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46059 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46059 / 40000) = 1/(40000 / 46059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (141043729 / 1000000000) (14104373 / 100000000) (Real.log (46059 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (46059 / 40000) = -Real.log (40000 / 46059) := by
    rw [show ((46059 / 40000) : ℝ) = ((40000 / 46059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (16425573 / 100000000) ≤ -Real.log (33941 / 40000) ∧
    -Real.log (33941 / 40000) ≤ (164255731 / 1000000000) := by
  have h := checkLog_sound (w := (6059 / 73941)) (n := 12)
    (lo := (16425573 / 100000000)) (hi := (164255731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 33941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 33941) = 1/(33941 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-164255731 / 1000000000) (-16425573 / 100000000) (Real.log (33941 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17663897 / 125000000) ≤ -Real.log (1000000 / 1151783) ∧
    -Real.log (1000000 / 1151783) ≤ (141311177 / 1000000000) := by
  have h := checkLog_sound (w := (151783 / 2151783)) (n := 12)
    (lo := (17663897 / 125000000)) (hi := (141311177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151783 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1151783 / 1000000) = 1/(1000000 / 1151783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17663897 / 125000000) (141311177 / 1000000000) (Real.log (1151783 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1151783 / 1000000) = -Real.log (1000000 / 1151783) := by
    rw [show ((1151783 / 1000000) : ℝ) = ((1000000 / 1151783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (164618779 / 1000000000) ≤ -Real.log (848217 / 1000000) ∧
    -Real.log (848217 / 1000000) ≤ (8230939 / 50000000) := by
  have h := checkLog_sound (w := (151783 / 1848217)) (n := 12)
    (lo := (164618779 / 1000000000)) (hi := (8230939 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 848217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 848217) = 1/(848217 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-8230939 / 50000000) (-164618779 / 1000000000) (Real.log (848217 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (614749381 / 1000000000) ≤ -Real.log (100000000000 / 184919309961) ∧
    -Real.log (100000000000 / 184919309961) ≤ (307374691 / 500000000) := by
  have h := checkLog_sound (w := (84919309961 / 284919309961)) (n := 12)
    (lo := (614749381 / 1000000000)) (hi := (307374691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184919309961 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184919309961 / 100000000000) = 1/(100000000000 / 184919309961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (614749381 / 1000000000) (307374691 / 500000000) (Real.log (184919309961 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (184919309961 / 100000000000) = -Real.log (100000000000 / 184919309961) := by
    rw [show ((184919309961 / 100000000000) : ℝ) = ((100000000000 / 184919309961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (77004469 / 125000000) ≤ -Real.log (100000000000 / 185157337789) ∧
    -Real.log (100000000000 / 185157337789) ≤ (616035753 / 1000000000) := by
  have h := checkLog_sound (w := (85157337789 / 285157337789)) (n := 12)
    (lo := (77004469 / 125000000)) (hi := (616035753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185157337789 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185157337789 / 100000000000) = 1/(100000000000 / 185157337789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (77004469 / 125000000) (616035753 / 1000000000) (Real.log (185157337789 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (185157337789 / 100000000000) = -Real.log (100000000000 / 185157337789) := by
    rw [show ((185157337789 / 100000000000) : ℝ) = ((100000000000 / 185157337789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (53701231 / 125000000) ≤ -Real.log (500000000000 / 768328938573) ∧
    -Real.log (500000000000 / 768328938573) ≤ (429609849 / 1000000000) := by
  have h := checkLog_sound (w := (268328938573 / 1268328938573)) (n := 12)
    (lo := (53701231 / 125000000)) (hi := (429609849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768328938573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768328938573 / 500000000000) = 1/(500000000000 / 768328938573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (53701231 / 125000000) (429609849 / 1000000000) (Real.log (768328938573 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (768328938573 / 500000000000) = -Real.log (500000000000 / 768328938573) := by
    rw [show ((768328938573 / 500000000000) : ℝ) = ((500000000000 / 768328938573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53811161 / 125000000) ≤ -Real.log (500000000000 / 769004935161) ∧
    -Real.log (500000000000 / 769004935161) ≤ (430489289 / 1000000000) := by
  have h := checkLog_sound (w := (269004935161 / 1269004935161)) (n := 12)
    (lo := (53811161 / 125000000)) (hi := (430489289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769004935161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(769004935161 / 500000000000) = 1/(500000000000 / 769004935161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (53811161 / 125000000) (430489289 / 1000000000) (Real.log (769004935161 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (769004935161 / 500000000000) = -Real.log (500000000000 / 769004935161) := by
    rw [show ((769004935161 / 500000000000) : ℝ) = ((500000000000 / 769004935161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (15264973 / 50000000) ≤ -Real.log (250000000000 / 339257829763) ∧
    -Real.log (250000000000 / 339257829763) ≤ (305299461 / 1000000000) := by
  have h := checkLog_sound (w := (89257829763 / 589257829763)) (n := 12)
    (lo := (15264973 / 50000000)) (hi := (305299461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339257829763 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339257829763 / 250000000000) = 1/(250000000000 / 339257829763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (15264973 / 50000000) (305299461 / 1000000000) (Real.log (339257829763 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (339257829763 / 250000000000) = -Real.log (250000000000 / 339257829763) := by
    rw [show ((339257829763 / 250000000000) : ℝ) = ((250000000000 / 339257829763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (76482489 / 250000000) ≤ -Real.log (250000000000 / 339471797901) ∧
    -Real.log (250000000000 / 339471797901) ≤ (305929957 / 1000000000) := by
  have h := checkLog_sound (w := (89471797901 / 589471797901)) (n := 12)
    (lo := (76482489 / 250000000)) (hi := (305929957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339471797901 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339471797901 / 250000000000) = 1/(250000000000 / 339471797901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (76482489 / 250000000) (305929957 / 1000000000) (Real.log (339471797901 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (339471797901 / 250000000000) = -Real.log (250000000000 / 339471797901) := by
    rw [show ((339471797901 / 250000000000) : ℝ) = ((250000000000 / 339471797901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (23307603 / 1000000000) ≤ -Real.log (976961920911 / 1000000000000) ∧
    -Real.log (976961920911 / 1000000000000) ≤ (5826901 / 250000000) := by
  have h := checkLog_sound (w := (23038079089 / 1976961920911)) (n := 12)
    (lo := (23307603 / 1000000000)) (hi := (5826901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976961920911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976961920911) = 1/(976961920911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5826901 / 250000000) (-23307603 / 1000000000) (Real.log (976961920911 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (23212001 / 1000000000) ≤ -Real.log (1563288519 / 1600000000) ∧
    -Real.log (1563288519 / 1600000000) ≤ (11606001 / 500000000) := by
  have h := checkLog_sound (w := (36711481 / 3163288519)) (n := 12)
    (lo := (23212001 / 1000000000)) (hi := (11606001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1563288519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1563288519) = 1/(1563288519 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-11606001 / 500000000) (-23212001 / 1000000000) (Real.log (1563288519 / 1600000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell082
