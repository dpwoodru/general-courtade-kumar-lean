import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell086
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

theorem reflection_log_1_neg : (16444699 / 62500000) ≤ -Real.log (5120 / 6661) ∧
    -Real.log (5120 / 6661) ≤ (52623037 / 200000000) := by
  have h := checkLog_sound (w := (1541 / 11781)) (n := 12)
    (lo := (16444699 / 62500000)) (hi := (52623037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6661 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6661 / 5120) = 1/(5120 / 6661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (16444699 / 62500000) (52623037 / 200000000) (Real.log (6661 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6661 / 5120) = -Real.log (5120 / 6661) := by
    rw [show ((6661 / 5120) : ℝ) = ((5120 / 6661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (358071007 / 1000000000) ≤ -Real.log (3579 / 5120) ∧
    -Real.log (3579 / 5120) ≤ (11189719 / 31250000) := by
  have h := checkLog_sound (w := (1541 / 8699)) (n := 12)
    (lo := (358071007 / 1000000000)) (hi := (11189719 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3579) = 1/(3579 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-11189719 / 31250000) (-358071007 / 1000000000) (Real.log (3579 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (2626647 / 10000000) ≤ -Real.log (2560 / 3329) ∧
    -Real.log (2560 / 3329) ≤ (262664701 / 1000000000) := by
  have h := checkLog_sound (w := (769 / 5889)) (n := 12)
    (lo := (2626647 / 10000000)) (hi := (262664701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3329 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3329 / 2560) = 1/(2560 / 3329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (2626647 / 10000000) (262664701 / 1000000000) (Real.log (3329 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3329 / 2560) = -Real.log (2560 / 3329) := by
    rw [show ((3329 / 2560) : ℝ) = ((2560 / 3329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (71446627 / 200000000) ≤ -Real.log (1791 / 2560) ∧
    -Real.log (1791 / 2560) ≤ (22327071 / 62500000) := by
  have h := checkLog_sound (w := (769 / 4351)) (n := 12)
    (lo := (71446627 / 200000000)) (hi := (22327071 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1791) = 1/(1791 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-22327071 / 62500000) (-71446627 / 200000000) (Real.log (1791 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (96646409 / 500000000) ≤ -Real.log (500000 / 606619) ∧
    -Real.log (500000 / 606619) ≤ (193292819 / 1000000000) := by
  have h := checkLog_sound (w := (106619 / 1106619)) (n := 12)
    (lo := (96646409 / 500000000)) (hi := (193292819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606619 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606619 / 500000) = 1/(500000 / 606619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (96646409 / 500000000) (193292819 / 1000000000) (Real.log (606619 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (606619 / 500000) = -Real.log (500000 / 606619) := by
    rw [show ((606619 / 500000) : ℝ) = ((500000 / 606619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (23982949 / 100000000) ≤ -Real.log (393381 / 500000) ∧
    -Real.log (393381 / 500000) ≤ (239829491 / 1000000000) := by
  have h := checkLog_sound (w := (106619 / 893381)) (n := 12)
    (lo := (23982949 / 100000000)) (hi := (239829491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393381) = 1/(393381 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-239829491 / 1000000000) (-23982949 / 100000000) (Real.log (393381 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (193638939 / 1000000000) ≤ -Real.log (500000 / 606829) ∧
    -Real.log (500000 / 606829) ≤ (9681947 / 50000000) := by
  have h := checkLog_sound (w := (106829 / 1106829)) (n := 12)
    (lo := (193638939 / 1000000000)) (hi := (9681947 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606829 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606829 / 500000) = 1/(500000 / 606829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (193638939 / 1000000000) (9681947 / 50000000) (Real.log (606829 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (606829 / 500000) = -Real.log (500000 / 606829) := by
    rw [show ((606829 / 500000) : ℝ) = ((500000 / 606829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (120181733 / 500000000) ≤ -Real.log (393171 / 500000) ∧
    -Real.log (393171 / 500000) ≤ (240363467 / 1000000000) := by
  have h := checkLog_sound (w := (106829 / 893171)) (n := 12)
    (lo := (120181733 / 500000000)) (hi := (240363467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393171) = 1/(393171 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-240363467 / 1000000000) (-120181733 / 500000000) (Real.log (393171 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (142112221 / 1000000000) ≤ -Real.log (500000 / 576353) ∧
    -Real.log (500000 / 576353) ≤ (71056111 / 500000000) := by
  have h := checkLog_sound (w := (76353 / 1076353)) (n := 12)
    (lo := (142112221 / 1000000000)) (hi := (71056111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576353 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(576353 / 500000) = 1/(500000 / 576353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (142112221 / 1000000000) (71056111 / 500000000) (Real.log (576353 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (576353 / 500000) = -Real.log (500000 / 576353) := by
    rw [show ((576353 / 500000) : ℝ) = ((500000 / 576353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (165707537 / 1000000000) ≤ -Real.log (423647 / 500000) ∧
    -Real.log (423647 / 500000) ≤ (82853769 / 500000000) := by
  have h := checkLog_sound (w := (76353 / 923647)) (n := 12)
    (lo := (165707537 / 1000000000)) (hi := (82853769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 423647) = 1/(423647 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-82853769 / 500000000) (-165707537 / 1000000000) (Real.log (423647 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (569521 / 4000000) ≤ -Real.log (200000 / 230603) ∧
    -Real.log (200000 / 230603) ≤ (142380251 / 1000000000) := by
  have h := checkLog_sound (w := (30603 / 430603)) (n := 12)
    (lo := (569521 / 4000000)) (hi := (142380251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230603 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230603 / 200000) = 1/(200000 / 230603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (569521 / 4000000) (142380251 / 1000000000) (Real.log (230603 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (230603 / 200000) = -Real.log (200000 / 230603) := by
    rw [show ((230603 / 200000) : ℝ) = ((200000 / 230603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (83036147 / 500000000) ≤ -Real.log (169397 / 200000) ∧
    -Real.log (169397 / 200000) ≤ (33214459 / 200000000) := by
  have h := checkLog_sound (w := (30603 / 369397)) (n := 12)
    (lo := (83036147 / 500000000)) (hi := (33214459 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 169397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 169397) = 1/(169397 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-33214459 / 200000000) (-83036147 / 500000000) (Real.log (169397 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (123979567 / 200000000) ≤ -Real.log (12500000000 / 23234226689) ∧
    -Real.log (12500000000 / 23234226689) ≤ (154974459 / 250000000) := by
  have h := checkLog_sound (w := (10734226689 / 35734226689)) (n := 12)
    (lo := (123979567 / 200000000)) (hi := (154974459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23234226689 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23234226689 / 12500000000) = 1/(12500000000 / 23234226689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (123979567 / 200000000) (154974459 / 250000000) (Real.log (23234226689 / 12500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (23234226689 / 12500000000) = -Real.log (12500000000 / 23234226689) := by
    rw [show ((23234226689 / 12500000000) : ℝ) = ((12500000000 / 23234226689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (621186191 / 1000000000) ≤ -Real.log (250000000000 / 465283598771) ∧
    -Real.log (250000000000 / 465283598771) ≤ (38824137 / 62500000) := by
  have h := checkLog_sound (w := (215283598771 / 715283598771)) (n := 12)
    (lo := (621186191 / 1000000000)) (hi := (38824137 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((465283598771 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(465283598771 / 250000000000) = 1/(250000000000 / 465283598771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (621186191 / 1000000000) (38824137 / 62500000) (Real.log (465283598771 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (465283598771 / 250000000000) = -Real.log (250000000000 / 465283598771) := by
    rw [show ((465283598771 / 250000000000) : ℝ) = ((250000000000 / 465283598771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (108280577 / 250000000) ≤ -Real.log (31250000000 / 48189525549) ∧
    -Real.log (31250000000 / 48189525549) ≤ (433122309 / 1000000000) := by
  have h := checkLog_sound (w := (16939525549 / 79439525549)) (n := 12)
    (lo := (108280577 / 250000000)) (hi := (433122309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48189525549 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48189525549 / 31250000000) = 1/(31250000000 / 48189525549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (108280577 / 250000000) (433122309 / 1000000000) (Real.log (48189525549 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (48189525549 / 31250000000) = -Real.log (31250000000 / 48189525549) := by
    rw [show ((48189525549 / 31250000000) : ℝ) = ((31250000000 / 48189525549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (217001203 / 500000000) ≤ -Real.log (62500000000 / 96463911377) ∧
    -Real.log (62500000000 / 96463911377) ≤ (434002407 / 1000000000) := by
  have h := checkLog_sound (w := (33963911377 / 158963911377)) (n := 12)
    (lo := (217001203 / 500000000)) (hi := (434002407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96463911377 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96463911377 / 62500000000) = 1/(62500000000 / 96463911377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (217001203 / 500000000) (434002407 / 1000000000) (Real.log (96463911377 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (96463911377 / 62500000000) = -Real.log (62500000000 / 96463911377) := by
    rw [show ((96463911377 / 62500000000) : ℝ) = ((62500000000 / 96463911377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (153909879 / 500000000) ≤ -Real.log (250000000000 / 340113939199) ∧
    -Real.log (250000000000 / 340113939199) ≤ (307819759 / 1000000000) := by
  have h := checkLog_sound (w := (90113939199 / 590113939199)) (n := 12)
    (lo := (153909879 / 500000000)) (hi := (307819759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340113939199 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340113939199 / 250000000000) = 1/(250000000000 / 340113939199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (153909879 / 500000000) (307819759 / 1000000000) (Real.log (340113939199 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (340113939199 / 250000000000) = -Real.log (250000000000 / 340113939199) := by
    rw [show ((340113939199 / 250000000000) : ℝ) = ((250000000000 / 340113939199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4819571 / 15625000) ≤ -Real.log (25000000000 / 34032922661) ∧
    -Real.log (25000000000 / 34032922661) ≤ (61690509 / 200000000) := by
  have h := checkLog_sound (w := (9032922661 / 59032922661)) (n := 12)
    (lo := (4819571 / 15625000)) (hi := (61690509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34032922661 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34032922661 / 25000000000) = 1/(25000000000 / 34032922661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4819571 / 15625000) (61690509 / 200000000) (Real.log (34032922661 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (34032922661 / 25000000000) = -Real.log (25000000000 / 34032922661) := by
    rw [show ((34032922661 / 25000000000) : ℝ) = ((25000000000 / 34032922661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (23692043 / 1000000000) ≤ -Real.log (39063456391 / 40000000000) ∧
    -Real.log (39063456391 / 40000000000) ≤ (5923011 / 250000000) := by
  have h := checkLog_sound (w := (936543609 / 79063456391)) (n := 12)
    (lo := (23692043 / 1000000000)) (hi := (5923011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39063456391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39063456391) = 1/(39063456391 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5923011 / 250000000) (-23692043 / 1000000000) (Real.log (39063456391 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4719063 / 200000000) ≤ -Real.log (244170219391 / 250000000000) ∧
    -Real.log (244170219391 / 250000000000) ≤ (5898829 / 250000000) := by
  have h := checkLog_sound (w := (5829780609 / 494170219391)) (n := 12)
    (lo := (4719063 / 200000000)) (hi := (5898829 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244170219391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244170219391) = 1/(244170219391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5898829 / 250000000) (-4719063 / 200000000) (Real.log (244170219391 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell086
