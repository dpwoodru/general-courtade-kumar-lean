import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell076
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

theorem reflection_log_1_neg : (258601183 / 1000000000) ≤ -Real.log (5120 / 6631) ∧
    -Real.log (5120 / 6631) ≤ (8081287 / 31250000) := by
  have h := checkLog_sound (w := (1511 / 11751)) (n := 12)
    (lo := (258601183 / 1000000000)) (hi := (8081287 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6631 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6631 / 5120) = 1/(5120 / 6631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (258601183 / 1000000000) (8081287 / 31250000) (Real.log (6631 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6631 / 5120) = -Real.log (5120 / 6631) := by
    rw [show ((6631 / 5120) : ℝ) = ((5120 / 6631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (349723713 / 1000000000) ≤ -Real.log (3609 / 5120) ∧
    -Real.log (3609 / 5120) ≤ (174861857 / 500000000) := by
  have h := checkLog_sound (w := (1511 / 8729)) (n := 12)
    (lo := (349723713 / 1000000000)) (hi := (174861857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3609) = 1/(3609 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-174861857 / 500000000) (-349723713 / 1000000000) (Real.log (3609 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12907433 / 50000000) ≤ -Real.log (1280 / 1657) ∧
    -Real.log (1280 / 1657) ≤ (258148661 / 1000000000) := by
  have h := checkLog_sound (w := (377 / 2937)) (n := 12)
    (lo := (12907433 / 50000000)) (hi := (258148661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1657 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1657 / 1280) = 1/(1280 / 1657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12907433 / 50000000) (258148661 / 1000000000) (Real.log (1657 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1657 / 1280) = -Real.log (1280 / 1657) := by
    rw [show ((1657 / 1280) : ℝ) = ((1280 / 1657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (348892803 / 1000000000) ≤ -Real.log (903 / 1280) ∧
    -Real.log (903 / 1280) ≤ (87223201 / 250000000) := by
  have h := checkLog_sound (w := (377 / 2183)) (n := 12)
    (lo := (348892803 / 1000000000)) (hi := (87223201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 903) = 1/(903 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-87223201 / 250000000) (-348892803 / 1000000000) (Real.log (903 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (189830791 / 1000000000) ≤ -Real.log (200000 / 241809) ∧
    -Real.log (200000 / 241809) ≤ (23728849 / 125000000) := by
  have h := checkLog_sound (w := (41809 / 441809)) (n := 12)
    (lo := (189830791 / 1000000000)) (hi := (23728849 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241809 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241809 / 200000) = 1/(200000 / 241809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (189830791 / 1000000000) (23728849 / 125000000) (Real.log (241809 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (241809 / 200000) = -Real.log (200000 / 241809) := by
    rw [show ((241809 / 200000) : ℝ) = ((200000 / 241809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (117257101 / 500000000) ≤ -Real.log (158191 / 200000) ∧
    -Real.log (158191 / 200000) ≤ (234514203 / 1000000000) := by
  have h := checkLog_sound (w := (41809 / 358191)) (n := 12)
    (lo := (117257101 / 500000000)) (hi := (234514203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158191) = 1/(158191 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-234514203 / 1000000000) (-117257101 / 500000000) (Real.log (158191 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (190178939 / 1000000000) ≤ -Real.log (500000 / 604733) ∧
    -Real.log (500000 / 604733) ≤ (9508947 / 50000000) := by
  have h := checkLog_sound (w := (104733 / 1104733)) (n := 12)
    (lo := (190178939 / 1000000000)) (hi := (9508947 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604733 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604733 / 500000) = 1/(500000 / 604733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (190178939 / 1000000000) (9508947 / 50000000) (Real.log (604733 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (604733 / 500000) = -Real.log (500000 / 604733) := by
    rw [show ((604733 / 500000) : ℝ) = ((500000 / 604733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (58761653 / 250000000) ≤ -Real.log (395267 / 500000) ∧
    -Real.log (395267 / 500000) ≤ (235046613 / 1000000000) := by
  have h := checkLog_sound (w := (104733 / 895267)) (n := 12)
    (lo := (58761653 / 250000000)) (hi := (235046613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 395267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 395267) = 1/(395267 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-235046613 / 1000000000) (-58761653 / 250000000) (Real.log (395267 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (139440151 / 1000000000) ≤ -Real.log (100000 / 114963) ∧
    -Real.log (100000 / 114963) ≤ (17430019 / 125000000) := by
  have h := checkLog_sound (w := (14963 / 214963)) (n := 12)
    (lo := (139440151 / 1000000000)) (hi := (17430019 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114963 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114963 / 100000) = 1/(100000 / 114963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (139440151 / 1000000000) (17430019 / 125000000) (Real.log (114963 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (114963 / 100000) = -Real.log (100000 / 114963) := by
    rw [show ((114963 / 100000) : ℝ) = ((100000 / 114963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (16208373 / 100000000) ≤ -Real.log (85037 / 100000) ∧
    -Real.log (85037 / 100000) ≤ (162083731 / 1000000000) := by
  have h := checkLog_sound (w := (14963 / 185037)) (n := 12)
    (lo := (16208373 / 100000000)) (hi := (162083731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 85037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 85037) = 1/(85037 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-162083731 / 1000000000) (-16208373 / 100000000) (Real.log (85037 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (139708027 / 1000000000) ≤ -Real.log (500000 / 574969) ∧
    -Real.log (500000 / 574969) ≤ (34927007 / 250000000) := by
  have h := checkLog_sound (w := (74969 / 1074969)) (n := 12)
    (lo := (139708027 / 1000000000)) (hi := (34927007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((574969 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(574969 / 500000) = 1/(500000 / 574969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (139708027 / 1000000000) (34927007 / 250000000) (Real.log (574969 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (574969 / 500000) = -Real.log (500000 / 574969) := by
    rw [show ((574969 / 500000) : ℝ) = ((500000 / 574969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (16244599 / 100000000) ≤ -Real.log (425031 / 500000) ∧
    -Real.log (425031 / 500000) ≤ (162445991 / 1000000000) := by
  have h := checkLog_sound (w := (74969 / 925031)) (n := 12)
    (lo := (16244599 / 100000000)) (hi := (162445991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 425031) = 1/(425031 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-162445991 / 1000000000) (-16244599 / 100000000) (Real.log (425031 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (75880183 / 125000000) ≤ -Real.log (10000000000 / 18349944629) ∧
    -Real.log (10000000000 / 18349944629) ≤ (121408293 / 200000000) := by
  have h := checkLog_sound (w := (8349944629 / 28349944629)) (n := 12)
    (lo := (75880183 / 125000000)) (hi := (121408293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18349944629 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18349944629 / 10000000000) = 1/(10000000000 / 18349944629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (75880183 / 125000000) (121408293 / 200000000) (Real.log (18349944629 / 10000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (18349944629 / 10000000000) = -Real.log (10000000000 / 18349944629) := by
    rw [show ((18349944629 / 10000000000) : ℝ) = ((10000000000 / 18349944629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (19010153 / 31250000) ≤ -Real.log (500000000000 / 918675533389) ∧
    -Real.log (500000000000 / 918675533389) ≤ (608324897 / 1000000000) := by
  have h := checkLog_sound (w := (418675533389 / 1418675533389)) (n := 12)
    (lo := (19010153 / 31250000)) (hi := (608324897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((918675533389 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(918675533389 / 500000000000) = 1/(500000000000 / 918675533389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (19010153 / 31250000) (608324897 / 1000000000) (Real.log (918675533389 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (918675533389 / 500000000000) = -Real.log (500000000000 / 918675533389) := by
    rw [show ((918675533389 / 500000000000) : ℝ) = ((500000000000 / 918675533389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (212172497 / 500000000) ≤ -Real.log (250000000000 / 382147214443) ∧
    -Real.log (250000000000 / 382147214443) ≤ (84868999 / 200000000) := by
  have h := checkLog_sound (w := (132147214443 / 632147214443)) (n := 12)
    (lo := (212172497 / 500000000)) (hi := (84868999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382147214443 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(382147214443 / 250000000000) = 1/(250000000000 / 382147214443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (212172497 / 500000000) (84868999 / 200000000) (Real.log (382147214443 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (382147214443 / 250000000000) = -Real.log (250000000000 / 382147214443) := by
    rw [show ((382147214443 / 250000000000) : ℝ) = ((250000000000 / 382147214443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (26576597 / 62500000) ≤ -Real.log (250000000000 / 382483865337) ∧
    -Real.log (250000000000 / 382483865337) ≤ (425225553 / 1000000000) := by
  have h := checkLog_sound (w := (132483865337 / 632483865337)) (n := 12)
    (lo := (26576597 / 62500000)) (hi := (425225553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382483865337 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(382483865337 / 250000000000) = 1/(250000000000 / 382483865337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (26576597 / 62500000) (425225553 / 1000000000) (Real.log (382483865337 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (382483865337 / 250000000000) = -Real.log (250000000000 / 382483865337) := by
    rw [show ((382483865337 / 250000000000) : ℝ) = ((250000000000 / 382483865337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (301523881 / 1000000000) ≤ -Real.log (50000000000 / 67595870033) ∧
    -Real.log (50000000000 / 67595870033) ≤ (150761941 / 500000000) := by
  have h := checkLog_sound (w := (17595870033 / 117595870033)) (n := 12)
    (lo := (301523881 / 1000000000)) (hi := (150761941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67595870033 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67595870033 / 50000000000) = 1/(50000000000 / 67595870033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (301523881 / 1000000000) (150761941 / 500000000) (Real.log (67595870033 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (67595870033 / 50000000000) = -Real.log (50000000000 / 67595870033) := by
    rw [show ((67595870033 / 50000000000) : ℝ) = ((50000000000 / 67595870033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (151077009 / 500000000) ≤ -Real.log (250000000000 / 338192390673) ∧
    -Real.log (250000000000 / 338192390673) ≤ (302154019 / 1000000000) := by
  have h := checkLog_sound (w := (88192390673 / 588192390673)) (n := 12)
    (lo := (151077009 / 500000000)) (hi := (302154019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((338192390673 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(338192390673 / 250000000000) = 1/(250000000000 / 338192390673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (151077009 / 500000000) (302154019 / 1000000000) (Real.log (338192390673 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (338192390673 / 250000000000) = -Real.log (250000000000 / 338192390673) := by
    rw [show ((338192390673 / 250000000000) : ℝ) = ((250000000000 / 338192390673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (22737963 / 1000000000) ≤ -Real.log (244379649039 / 250000000000) ∧
    -Real.log (244379649039 / 250000000000) ≤ (5684491 / 250000000) := by
  have h := checkLog_sound (w := (5620350961 / 494379649039)) (n := 12)
    (lo := (22737963 / 1000000000)) (hi := (5684491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244379649039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244379649039) = 1/(244379649039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5684491 / 250000000) (-22737963 / 1000000000) (Real.log (244379649039 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (11321789 / 500000000) ≤ -Real.log (9776108631 / 10000000000) ∧
    -Real.log (9776108631 / 10000000000) ≤ (22643579 / 1000000000) := by
  have h := checkLog_sound (w := (223891369 / 19776108631)) (n := 12)
    (lo := (11321789 / 500000000)) (hi := (22643579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9776108631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9776108631) = 1/(9776108631 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-22643579 / 1000000000) (-11321789 / 500000000) (Real.log (9776108631 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell076
