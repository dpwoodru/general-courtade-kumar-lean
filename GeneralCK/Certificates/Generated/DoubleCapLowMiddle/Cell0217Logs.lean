import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0217
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

theorem reflection_log_1_neg : (534664213 / 1000000000) ≤ -Real.log (1600 / 2731) ∧
    -Real.log (1600 / 2731) ≤ (267332107 / 500000000) := by
  have h := checkLog_sound (w := (1131 / 4331)) (n := 12)
    (lo := (534664213 / 1000000000)) (hi := (267332107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2731 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2731 / 1600) = 1/(1600 / 2731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (534664213 / 1000000000) (267332107 / 500000000) (Real.log (2731 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2731 / 1600) = -Real.log (1600 / 2731) := by
    rw [show ((2731 / 1600) : ℝ) = ((1600 / 2731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1227156139 / 1000000000) ≤ -Real.log (469 / 1600) ∧
    -Real.log (469 / 1600) ≤ (1227156141 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1269)) (n := 12)
    (lo := (534008959 / 1000000000)) (hi := (834389 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 469) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 469) = 1/(469 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1227156141 / 1000000000) (-1227156139 / 1000000000) (Real.log (469 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (531179569 / 1000000000) ≤ -Real.log (3200 / 5443) ∧
    -Real.log (3200 / 5443) ≤ (53117957 / 100000000) := by
  have h := checkLog_sound (w := (2243 / 8643)) (n := 12)
    (lo := (531179569 / 1000000000)) (hi := (53117957 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5443 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5443 / 3200) = 1/(3200 / 5443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (531179569 / 1000000000) (53117957 / 100000000) (Real.log (5443 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5443 / 3200) = -Real.log (3200 / 5443) := by
    rw [show ((5443 / 3200) : ℝ) = ((3200 / 5443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (150887837 / 125000000) ≤ -Real.log (957 / 3200) ∧
    -Real.log (957 / 3200) ≤ (603551349 / 500000000) := by
  have h := checkLog_sound (w := (643 / 2557)) (n := 12)
    (lo := (128488879 / 250000000)) (hi := (513955517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 957) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 957) = 1/(957 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-603551349 / 500000000) (-150887837 / 125000000) (Real.log (957 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (86561437 / 250000000) ≤ -Real.log (800 / 1131) ∧
    -Real.log (800 / 1131) ≤ (346245749 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1931)) (n := 12)
    (lo := (86561437 / 250000000)) (hi := (346245749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131 / 800) = 1/(800 / 1131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (86561437 / 250000000) (346245749 / 1000000000) (Real.log (1131 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1131 / 800) = -Real.log (800 / 1131) := by
    rw [show ((1131 / 800) : ℝ) = ((800 / 1131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (534008959 / 1000000000) ≤ -Real.log (469 / 800) ∧
    -Real.log (469 / 800) ≤ (834389 / 1562500) := by
  have h := checkLog_sound (w := (331 / 1269)) (n := 12)
    (lo := (534008959 / 1000000000)) (hi := (834389 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 469) = 1/(469 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-834389 / 1562500) (-534008959 / 1000000000) (Real.log (469 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (168905313 / 500000000) ≤ -Real.log (1600 / 2243) ∧
    -Real.log (1600 / 2243) ≤ (337810627 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 3843)) (n := 12)
    (lo := (168905313 / 500000000)) (hi := (337810627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2243 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2243 / 1600) = 1/(1600 / 2243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (168905313 / 500000000) (337810627 / 1000000000) (Real.log (2243 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2243 / 1600) = -Real.log (1600 / 2243) := by
    rw [show ((2243 / 1600) : ℝ) = ((1600 / 2243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (128488879 / 250000000) ≤ -Real.log (957 / 1600) ∧
    -Real.log (957 / 1600) ≤ (513955517 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 2557)) (n := 12)
    (lo := (128488879 / 250000000)) (hi := (513955517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 957) = 1/(957 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-513955517 / 1000000000) (-128488879 / 250000000) (Real.log (957 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (298823391 / 500000000) ≤ -Real.log (250000 / 454459) ∧
    -Real.log (250000 / 454459) ≤ (597646783 / 1000000000) := by
  have h := checkLog_sound (w := (204459 / 704459)) (n := 12)
    (lo := (298823391 / 500000000)) (hi := (597646783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((454459 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(454459 / 250000) = 1/(250000 / 454459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (298823391 / 500000000) (597646783 / 1000000000) (Real.log (454459 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (454459 / 250000) = -Real.log (250000 / 454459) := by
    rw [show ((454459 / 250000) : ℝ) = ((250000 / 454459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1702847897 / 1000000000) ≤ -Real.log (45541 / 250000) ∧
    -Real.log (45541 / 250000) ≤ (17028479 / 10000000) := by
  have h := checkLog_sound (w := (16959 / 108041)) (n := 12)
    (lo := (316553537 / 1000000000)) (hi := (158276769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45541) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 45541) = 1/(45541 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-17028479 / 10000000) (-1702847897 / 1000000000) (Real.log (45541 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (299436107 / 500000000) ≤ -Real.log (200000 / 364013) ∧
    -Real.log (200000 / 364013) ≤ (119774443 / 200000000) := by
  have h := checkLog_sound (w := (164013 / 564013)) (n := 12)
    (lo := (299436107 / 500000000)) (hi := (119774443 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364013 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364013 / 200000) = 1/(200000 / 364013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (299436107 / 500000000) (119774443 / 200000000) (Real.log (364013 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (364013 / 200000) = -Real.log (200000 / 364013) := by
    rw [show ((364013 / 200000) : ℝ) = ((200000 / 364013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1715159603 / 1000000000) ≤ -Real.log (35987 / 200000) ∧
    -Real.log (35987 / 200000) ≤ (857579803 / 500000000) := by
  have h := checkLog_sound (w := (14013 / 85987)) (n := 12)
    (lo := (328865243 / 1000000000)) (hi := (82216311 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35987) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 35987) = 1/(35987 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-857579803 / 500000000) (-1715159603 / 1000000000) (Real.log (35987 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (579282831 / 1000000000) ≤ -Real.log (500000 / 892379) ∧
    -Real.log (500000 / 892379) ≤ (36205177 / 62500000) := by
  have h := checkLog_sound (w := (392379 / 1392379)) (n := 12)
    (lo := (579282831 / 1000000000)) (hi := (36205177 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((892379 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(892379 / 500000) = 1/(500000 / 892379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (579282831 / 1000000000) (36205177 / 62500000) (Real.log (892379 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (892379 / 500000) = -Real.log (500000 / 892379) := by
    rw [show ((892379 / 500000) : ℝ) = ((500000 / 892379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1535992301 / 1000000000) ≤ -Real.log (107621 / 500000) ∧
    -Real.log (107621 / 500000) ≤ (95999519 / 62500000) := by
  have h := checkLog_sound (w := (17379 / 232621)) (n := 12)
    (lo := (149697941 / 1000000000)) (hi := (74848971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107621) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 107621) = 1/(107621 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-95999519 / 62500000) (-1535992301 / 1000000000) (Real.log (107621 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (581432631 / 1000000000) ≤ -Real.log (1000000 / 1788599) ∧
    -Real.log (1000000 / 1788599) ≤ (72679079 / 125000000) := by
  have h := checkLog_sound (w := (788599 / 2788599)) (n := 12)
    (lo := (581432631 / 1000000000)) (hi := (72679079 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1788599 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1788599 / 1000000) = 1/(1000000 / 1788599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (581432631 / 1000000000) (72679079 / 125000000) (Real.log (1788599 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1788599 / 1000000) = -Real.log (1000000 / 1788599) := by
    rw [show ((1788599 / 1000000) : ℝ) = ((1000000 / 1788599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (776999237 / 500000000) ≤ -Real.log (211401 / 1000000) ∧
    -Real.log (211401 / 1000000) ≤ (1553998477 / 1000000000) := by
  have h := checkLog_sound (w := (38599 / 461401)) (n := 12)
    (lo := (83852057 / 500000000)) (hi := (33540823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 211401) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 211401) = 1/(211401 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1553998477 / 1000000000) (-776999237 / 500000000) (Real.log (211401 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2300494679 / 1000000000) ≤ -Real.log (10000000000 / 99791177181) ∧
    -Real.log (10000000000 / 99791177181) ≤ (2300494683 / 1000000000) := by
  have h := checkLog_sound (w := (19791177181 / 179791177181)) (n := 12)
    (lo := (221053139 / 1000000000)) (hi := (11052657 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99791177181 / 80000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(99791177181 / 80000000000) = 1/(10000000000 / 99791177181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2300494679 / 1000000000) (2300494683 / 1000000000) (Real.log (99791177181 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (99791177181 / 10000000000) = -Real.log (10000000000 / 99791177181) := by
    rw [show ((99791177181 / 10000000000) : ℝ) = ((10000000000 / 99791177181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2314031817 / 1000000000) ≤ -Real.log (500000000000 / 5057562453109) ∧
    -Real.log (500000000000 / 5057562453109) ≤ (2314031821 / 1000000000) := by
  have h := checkLog_sound (w := (1057562453109 / 9057562453109)) (n := 12)
    (lo := (234590277 / 1000000000)) (hi := (117295139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5057562453109 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5057562453109 / 4000000000000) = 1/(500000000000 / 5057562453109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2314031817 / 1000000000) (2314031821 / 1000000000) (Real.log (5057562453109 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5057562453109 / 500000000000) = -Real.log (500000000000 / 5057562453109) := by
    rw [show ((5057562453109 / 500000000000) : ℝ) = ((500000000000 / 5057562453109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (528818783 / 250000000) ≤ -Real.log (250000000000 / 2072966707241) ∧
    -Real.log (250000000000 / 2072966707241) ≤ (16525587 / 7812500) := by
  have h := checkLog_sound (w := (72966707241 / 4072966707241)) (n := 12)
    (lo := (4479199 / 125000000)) (hi := (35833593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2072966707241 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2072966707241 / 2000000000000) = 1/(250000000000 / 2072966707241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (528818783 / 250000000) (16525587 / 7812500) (Real.log (2072966707241 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2072966707241 / 250000000000) = -Real.log (250000000000 / 2072966707241) := by
    rw [show ((2072966707241 / 250000000000) : ℝ) = ((250000000000 / 2072966707241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (427086221 / 200000000) ≤ -Real.log (100000000000 / 846069318499) ∧
    -Real.log (100000000000 / 846069318499) ≤ (2135431109 / 1000000000) := by
  have h := checkLog_sound (w := (46069318499 / 1646069318499)) (n := 12)
    (lo := (11197913 / 200000000)) (hi := (27994783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((846069318499 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(846069318499 / 800000000000) = 1/(100000000000 / 846069318499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (427086221 / 200000000) (2135431109 / 1000000000) (Real.log (846069318499 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (846069318499 / 100000000000) = -Real.log (100000000000 / 846069318499) := by
    rw [show ((846069318499 / 100000000000) : ℝ) = ((100000000000 / 846069318499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0217
