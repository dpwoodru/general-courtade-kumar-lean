import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell128
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

theorem reflection_log_1_neg : (140927289 / 500000000) ≤ -Real.log (5120 / 6787) ∧
    -Real.log (5120 / 6787) ≤ (281854579 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 11907)) (n := 12)
    (lo := (140927289 / 500000000)) (hi := (281854579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6787 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6787 / 5120) = 1/(5120 / 6787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (140927289 / 500000000) (281854579 / 1000000000) (Real.log (6787 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6787 / 5120) = -Real.log (5120 / 6787) := by
    rw [show ((6787 / 5120) : ℝ) = ((5120 / 6787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (19695551 / 50000000) ≤ -Real.log (3453 / 5120) ∧
    -Real.log (3453 / 5120) ≤ (393911021 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 8573)) (n := 12)
    (lo := (19695551 / 50000000)) (hi := (393911021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3453) = 1/(3453 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-393911021 / 1000000000) (-19695551 / 50000000) (Real.log (3453 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (281412459 / 1000000000) ≤ -Real.log (40 / 53) ∧
    -Real.log (40 / 53) ≤ (14070623 / 50000000) := by
  have h := checkLog_sound (w := (13 / 93)) (n := 12)
    (lo := (281412459 / 1000000000)) (hi := (14070623 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53 / 40) = 1/(40 / 53) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (281412459 / 1000000000) (14070623 / 50000000) (Real.log (53 / 40)) := by
  have h := reflection_log_3_neg
  have he : Real.log (53 / 40) = -Real.log (40 / 53) := by
    rw [show ((53 / 40) : ℝ) = ((40 / 53) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (98260647 / 250000000) ≤ -Real.log (27 / 40) ∧
    -Real.log (27 / 40) ≤ (393042589 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 27) = 1/(27 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-393042589 / 1000000000) (-98260647 / 250000000) (Real.log (27 / 40)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (207718799 / 1000000000) ≤ -Real.log (1000000 / 1230867) ∧
    -Real.log (1000000 / 1230867) ≤ (519297 / 2500000) := by
  have h := checkLog_sound (w := (230867 / 2230867)) (n := 12)
    (lo := (207718799 / 1000000000)) (hi := (519297 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1230867 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1230867 / 1000000) = 1/(1000000 / 1230867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (207718799 / 1000000000) (519297 / 2500000) (Real.log (1230867 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1230867 / 1000000) = -Real.log (1000000 / 1230867) := by
    rw [show ((1230867 / 1000000) : ℝ) = ((1000000 / 1230867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (65622843 / 250000000) ≤ -Real.log (769133 / 1000000) ∧
    -Real.log (769133 / 1000000) ≤ (262491373 / 1000000000) := by
  have h := checkLog_sound (w := (230867 / 1769133)) (n := 12)
    (lo := (65622843 / 250000000)) (hi := (262491373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 769133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 769133) = 1/(769133 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-262491373 / 1000000000) (-65622843 / 250000000) (Real.log (769133 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (52015397 / 250000000) ≤ -Real.log (1000000 / 1231289) ∧
    -Real.log (1000000 / 1231289) ≤ (208061589 / 1000000000) := by
  have h := checkLog_sound (w := (231289 / 2231289)) (n := 12)
    (lo := (52015397 / 250000000)) (hi := (208061589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231289 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231289 / 1000000) = 1/(1000000 / 1231289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (52015397 / 250000000) (208061589 / 1000000000) (Real.log (1231289 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1231289 / 1000000) = -Real.log (1000000 / 1231289) := by
    rw [show ((1231289 / 1000000) : ℝ) = ((1000000 / 1231289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (4110003 / 15625000) ≤ -Real.log (768711 / 1000000) ∧
    -Real.log (768711 / 1000000) ≤ (263040193 / 1000000000) := by
  have h := checkLog_sound (w := (231289 / 1768711)) (n := 12)
    (lo := (4110003 / 15625000)) (hi := (263040193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 768711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 768711) = 1/(768711 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-263040193 / 1000000000) (-4110003 / 15625000) (Real.log (768711 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (6132699 / 40000000) ≤ -Real.log (200000 / 233139) ∧
    -Real.log (200000 / 233139) ≤ (38329369 / 250000000) := by
  have h := checkLog_sound (w := (33139 / 433139)) (n := 12)
    (lo := (6132699 / 40000000)) (hi := (38329369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233139 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233139 / 200000) = 1/(200000 / 233139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (6132699 / 40000000) (38329369 / 250000000) (Real.log (233139 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (233139 / 200000) = -Real.log (200000 / 233139) := by
    rw [show ((233139 / 200000) : ℝ) = ((200000 / 233139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (45289059 / 250000000) ≤ -Real.log (166861 / 200000) ∧
    -Real.log (166861 / 200000) ≤ (181156237 / 1000000000) := by
  have h := checkLog_sound (w := (33139 / 366861)) (n := 12)
    (lo := (45289059 / 250000000)) (hi := (181156237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 166861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 166861) = 1/(166861 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-181156237 / 1000000000) (-45289059 / 250000000) (Real.log (166861 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (153584233 / 1000000000) ≤ -Real.log (500000 / 583003) ∧
    -Real.log (500000 / 583003) ≤ (76792117 / 500000000) := by
  have h := checkLog_sound (w := (83003 / 1083003)) (n := 12)
    (lo := (153584233 / 1000000000)) (hi := (76792117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583003 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583003 / 500000) = 1/(500000 / 583003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (153584233 / 1000000000) (76792117 / 500000000) (Real.log (583003 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (583003 / 500000) = -Real.log (500000 / 583003) := by
    rw [show ((583003 / 500000) : ℝ) = ((500000 / 583003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18152907 / 100000000) ≤ -Real.log (416997 / 500000) ∧
    -Real.log (416997 / 500000) ≤ (181529071 / 1000000000) := by
  have h := checkLog_sound (w := (83003 / 916997)) (n := 12)
    (lo := (18152907 / 100000000)) (hi := (181529071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 416997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 416997) = 1/(416997 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-181529071 / 1000000000) (-18152907 / 100000000) (Real.log (416997 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (674455047 / 1000000000) ≤ -Real.log (500000000000 / 981481481481) ∧
    -Real.log (500000000000 / 981481481481) ≤ (84306881 / 125000000) := by
  have h := checkLog_sound (w := (481481481481 / 1481481481481)) (n := 12)
    (lo := (674455047 / 1000000000)) (hi := (84306881 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981481481481 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981481481481 / 500000000000) = 1/(500000000000 / 981481481481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (674455047 / 1000000000) (84306881 / 125000000) (Real.log (981481481481 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (981481481481 / 500000000000) = -Real.log (500000000000 / 981481481481) := by
    rw [show ((981481481481 / 500000000000) : ℝ) = ((500000000000 / 981481481481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (675765599 / 1000000000) ≤ -Real.log (500000000000 / 982768607009) ∧
    -Real.log (500000000000 / 982768607009) ≤ (844707 / 1250000) := by
  have h := checkLog_sound (w := (482768607009 / 1482768607009)) (n := 12)
    (lo := (675765599 / 1000000000)) (hi := (844707 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982768607009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982768607009 / 500000000000) = 1/(500000000000 / 982768607009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (675765599 / 1000000000) (844707 / 1250000) (Real.log (982768607009 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (982768607009 / 500000000000) = -Real.log (500000000000 / 982768607009) := by
    rw [show ((982768607009 / 500000000000) : ℝ) = ((500000000000 / 982768607009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (470210171 / 1000000000) ≤ -Real.log (500000000000 / 800165251003) ∧
    -Real.log (500000000000 / 800165251003) ≤ (117552543 / 250000000) := by
  have h := checkLog_sound (w := (300165251003 / 1300165251003)) (n := 12)
    (lo := (470210171 / 1000000000)) (hi := (117552543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800165251003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800165251003 / 500000000000) = 1/(500000000000 / 800165251003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (470210171 / 1000000000) (117552543 / 250000000) (Real.log (800165251003 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (800165251003 / 500000000000) = -Real.log (500000000000 / 800165251003) := by
    rw [show ((800165251003 / 500000000000) : ℝ) = ((500000000000 / 800165251003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (23555089 / 50000000) ≤ -Real.log (500000000000 / 800879003943) ∧
    -Real.log (500000000000 / 800879003943) ≤ (471101781 / 1000000000) := by
  have h := checkLog_sound (w := (300879003943 / 1300879003943)) (n := 12)
    (lo := (23555089 / 50000000)) (hi := (471101781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800879003943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800879003943 / 500000000000) = 1/(500000000000 / 800879003943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (23555089 / 50000000) (471101781 / 1000000000) (Real.log (800879003943 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (800879003943 / 500000000000) = -Real.log (500000000000 / 800879003943) := by
    rw [show ((800879003943 / 500000000000) : ℝ) = ((500000000000 / 800879003943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (334473711 / 1000000000) ≤ -Real.log (500000000000 / 698602429567) ∧
    -Real.log (500000000000 / 698602429567) ≤ (20904607 / 62500000) := by
  have h := checkLog_sound (w := (198602429567 / 1198602429567)) (n := 12)
    (lo := (334473711 / 1000000000)) (hi := (20904607 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698602429567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698602429567 / 500000000000) = 1/(500000000000 / 698602429567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (334473711 / 1000000000) (20904607 / 62500000) (Real.log (698602429567 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (698602429567 / 500000000000) = -Real.log (500000000000 / 698602429567) := by
    rw [show ((698602429567 / 500000000000) : ℝ) = ((500000000000 / 698602429567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (41889163 / 125000000) ≤ -Real.log (500000000000 / 699049393641) ∧
    -Real.log (500000000000 / 699049393641) ≤ (67022661 / 200000000) := by
  have h := checkLog_sound (w := (199049393641 / 1199049393641)) (n := 12)
    (lo := (41889163 / 125000000)) (hi := (67022661 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699049393641 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699049393641 / 500000000000) = 1/(500000000000 / 699049393641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (41889163 / 125000000) (67022661 / 200000000) (Real.log (699049393641 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (699049393641 / 500000000000) = -Real.log (500000000000 / 699049393641) := by
    rw [show ((699049393641 / 500000000000) : ℝ) = ((500000000000 / 699049393641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (27944837 / 1000000000) ≤ -Real.log (243110501991 / 250000000000) ∧
    -Real.log (243110501991 / 250000000000) ≤ (13972419 / 500000000) := by
  have h := checkLog_sound (w := (6889498009 / 493110501991)) (n := 12)
    (lo := (27944837 / 1000000000)) (hi := (13972419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243110501991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243110501991) = 1/(243110501991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-13972419 / 500000000) (-27944837 / 1000000000) (Real.log (243110501991 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (695969 / 25000000) ≤ -Real.log (38901806679 / 40000000000) ∧
    -Real.log (38901806679 / 40000000000) ≤ (27838761 / 1000000000) := by
  have h := checkLog_sound (w := (1098193321 / 78901806679)) (n := 12)
    (lo := (695969 / 25000000)) (hi := (27838761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38901806679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38901806679) = 1/(38901806679 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-27838761 / 1000000000) (-695969 / 25000000) (Real.log (38901806679 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell128
