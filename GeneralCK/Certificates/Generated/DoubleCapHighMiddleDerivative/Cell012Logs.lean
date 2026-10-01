import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell012
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

theorem reflection_log_1_neg : (229218809 / 1000000000) ≤ -Real.log (5120 / 6439) ∧
    -Real.log (5120 / 6439) ≤ (22921881 / 100000000) := by
  have h := checkLog_sound (w := (1319 / 11559)) (n := 12)
    (lo := (229218809 / 1000000000)) (hi := (22921881 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6439 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6439 / 5120) = 1/(5120 / 6439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (229218809 / 1000000000) (22921881 / 100000000) (Real.log (6439 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6439 / 5120) = -Real.log (5120 / 6439) := by
    rw [show ((6439 / 5120) : ℝ) = ((5120 / 6439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (297890249 / 1000000000) ≤ -Real.log (3801 / 5120) ∧
    -Real.log (3801 / 5120) ≤ (1191561 / 4000000) := by
  have h := checkLog_sound (w := (1319 / 8921)) (n := 12)
    (lo := (297890249 / 1000000000)) (hi := (1191561 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3801) = 1/(3801 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1191561 / 4000000) (-297890249 / 1000000000) (Real.log (3801 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (22875279 / 100000000) ≤ -Real.log (1280 / 1609) ∧
    -Real.log (1280 / 1609) ≤ (228752791 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 2889)) (n := 12)
    (lo := (22875279 / 100000000)) (hi := (228752791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1609 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1609 / 1280) = 1/(1280 / 1609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (22875279 / 100000000) (228752791 / 1000000000) (Real.log (1609 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1609 / 1280) = -Real.log (1280 / 1609) := by
    rw [show ((1609 / 1280) : ℝ) = ((1280 / 1609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (148550647 / 500000000) ≤ -Real.log (951 / 1280) ∧
    -Real.log (951 / 1280) ≤ (59420259 / 200000000) := by
  have h := checkLog_sound (w := (329 / 2231)) (n := 12)
    (lo := (148550647 / 500000000)) (hi := (59420259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 951) = 1/(951 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-59420259 / 200000000) (-148550647 / 500000000) (Real.log (951 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (10464347 / 62500000) ≤ -Real.log (500000 / 591131) ∧
    -Real.log (500000 / 591131) ≤ (167429553 / 1000000000) := by
  have h := checkLog_sound (w := (91131 / 1091131)) (n := 12)
    (lo := (10464347 / 62500000)) (hi := (167429553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591131 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591131 / 500000) = 1/(500000 / 591131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (10464347 / 62500000) (167429553 / 1000000000) (Real.log (591131 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (591131 / 500000) = -Real.log (500000 / 591131) := by
    rw [show ((591131 / 500000) : ℝ) = ((500000 / 591131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (201213287 / 1000000000) ≤ -Real.log (408869 / 500000) ∧
    -Real.log (408869 / 500000) ≤ (25151661 / 125000000) := by
  have h := checkLog_sound (w := (91131 / 908869)) (n := 12)
    (lo := (201213287 / 1000000000)) (hi := (25151661 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 408869) = 1/(408869 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-25151661 / 125000000) (-201213287 / 1000000000) (Real.log (408869 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (33556779 / 200000000) ≤ -Real.log (1000000 / 1182681) ∧
    -Real.log (1000000 / 1182681) ≤ (20972987 / 125000000) := by
  have h := checkLog_sound (w := (182681 / 2182681)) (n := 12)
    (lo := (33556779 / 200000000)) (hi := (20972987 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1182681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1182681 / 1000000) = 1/(1000000 / 1182681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (33556779 / 200000000) (20972987 / 125000000) (Real.log (1182681 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1182681 / 1000000) = -Real.log (1000000 / 1182681) := by
    rw [show ((1182681 / 1000000) : ℝ) = ((1000000 / 1182681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (201725807 / 1000000000) ≤ -Real.log (817319 / 1000000) ∧
    -Real.log (817319 / 1000000) ≤ (12607863 / 62500000) := by
  have h := checkLog_sound (w := (182681 / 1817319)) (n := 12)
    (lo := (201725807 / 1000000000)) (hi := (12607863 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 817319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 817319) = 1/(817319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12607863 / 62500000) (-201725807 / 1000000000) (Real.log (817319 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (122285771 / 1000000000) ≤ -Real.log (1000000 / 1130077) ∧
    -Real.log (1000000 / 1130077) ≤ (30571443 / 250000000) := by
  have h := checkLog_sound (w := (130077 / 2130077)) (n := 12)
    (lo := (122285771 / 1000000000)) (hi := (30571443 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1130077 / 1000000) = 1/(1000000 / 1130077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (122285771 / 1000000000) (30571443 / 250000000) (Real.log (1130077 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1130077 / 1000000) = -Real.log (1000000 / 1130077) := by
    rw [show ((1130077 / 1000000) : ℝ) = ((1000000 / 1130077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8709411 / 62500000) ≤ -Real.log (869923 / 1000000) ∧
    -Real.log (869923 / 1000000) ≤ (139350577 / 1000000000) := by
  have h := checkLog_sound (w := (130077 / 1869923)) (n := 12)
    (lo := (8709411 / 62500000)) (hi := (139350577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 869923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 869923) = 1/(869923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-139350577 / 1000000000) (-8709411 / 62500000) (Real.log (869923 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (15319343 / 125000000) ≤ -Real.log (1000000 / 1130381) ∧
    -Real.log (1000000 / 1130381) ≤ (24510949 / 200000000) := by
  have h := checkLog_sound (w := (130381 / 2130381)) (n := 12)
    (lo := (15319343 / 125000000)) (hi := (24510949 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1130381 / 1000000) = 1/(1000000 / 1130381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (15319343 / 125000000) (24510949 / 200000000) (Real.log (1130381 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1130381 / 1000000) = -Real.log (1000000 / 1130381) := by
    rw [show ((1130381 / 1000000) : ℝ) = ((1000000 / 1130381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (69850047 / 500000000) ≤ -Real.log (869619 / 1000000) ∧
    -Real.log (869619 / 1000000) ≤ (27940019 / 200000000) := by
  have h := checkLog_sound (w := (130381 / 1869619)) (n := 12)
    (lo := (69850047 / 500000000)) (hi := (27940019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 869619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 869619) = 1/(869619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-27940019 / 200000000) (-69850047 / 500000000) (Real.log (869619 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (131463521 / 250000000) ≤ -Real.log (500000000000 / 845951629863) ∧
    -Real.log (500000000000 / 845951629863) ≤ (105170817 / 200000000) := by
  have h := checkLog_sound (w := (345951629863 / 1345951629863)) (n := 12)
    (lo := (131463521 / 250000000)) (hi := (105170817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((845951629863 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(845951629863 / 500000000000) = 1/(500000000000 / 845951629863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (131463521 / 250000000) (105170817 / 200000000) (Real.log (845951629863 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (845951629863 / 500000000000) = -Real.log (500000000000 / 845951629863) := by
    rw [show ((845951629863 / 500000000000) : ℝ) = ((500000000000 / 845951629863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (263554529 / 500000000) ≤ -Real.log (5000000000 / 8470139437) ∧
    -Real.log (5000000000 / 8470139437) ≤ (527109059 / 1000000000) := by
  have h := checkLog_sound (w := (3470139437 / 13470139437)) (n := 12)
    (lo := (263554529 / 500000000)) (hi := (527109059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8470139437 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8470139437 / 5000000000) = 1/(5000000000 / 8470139437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (263554529 / 500000000) (527109059 / 1000000000) (Real.log (8470139437 / 5000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (8470139437 / 5000000000) = -Real.log (5000000000 / 8470139437) := by
    rw [show ((8470139437 / 5000000000) : ℝ) = ((5000000000 / 8470139437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (368642839 / 1000000000) ≤ -Real.log (100000000000 / 144577113941) ∧
    -Real.log (100000000000 / 144577113941) ≤ (9216071 / 25000000) := by
  have h := checkLog_sound (w := (44577113941 / 244577113941)) (n := 12)
    (lo := (368642839 / 1000000000)) (hi := (9216071 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144577113941 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144577113941 / 100000000000) = 1/(100000000000 / 144577113941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (368642839 / 1000000000) (9216071 / 25000000) (Real.log (144577113941 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (144577113941 / 100000000000) = -Real.log (100000000000 / 144577113941) := by
    rw [show ((144577113941 / 100000000000) : ℝ) = ((100000000000 / 144577113941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (184754851 / 500000000) ≤ -Real.log (50000000000 / 72351248411) ∧
    -Real.log (50000000000 / 72351248411) ≤ (369509703 / 1000000000) := by
  have h := checkLog_sound (w := (22351248411 / 122351248411)) (n := 12)
    (lo := (184754851 / 500000000)) (hi := (369509703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72351248411 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72351248411 / 50000000000) = 1/(50000000000 / 72351248411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (184754851 / 500000000) (369509703 / 1000000000) (Real.log (72351248411 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (72351248411 / 50000000000) = -Real.log (50000000000 / 72351248411) := by
    rw [show ((72351248411 / 50000000000) : ℝ) = ((50000000000 / 72351248411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (65409087 / 250000000) ≤ -Real.log (15625000000 / 20297719597) ∧
    -Real.log (15625000000 / 20297719597) ≤ (261636349 / 1000000000) := by
  have h := checkLog_sound (w := (4672719597 / 35922719597)) (n := 12)
    (lo := (65409087 / 250000000)) (hi := (261636349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20297719597 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20297719597 / 15625000000) = 1/(15625000000 / 20297719597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (65409087 / 250000000) (261636349 / 1000000000) (Real.log (20297719597 / 15625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (20297719597 / 15625000000) = -Real.log (15625000000 / 20297719597) := by
    rw [show ((20297719597 / 15625000000) : ℝ) = ((15625000000 / 20297719597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (131127419 / 500000000) ≤ -Real.log (500000000000 / 649928876899) ∧
    -Real.log (500000000000 / 649928876899) ≤ (262254839 / 1000000000) := by
  have h := checkLog_sound (w := (149928876899 / 1149928876899)) (n := 12)
    (lo := (131127419 / 500000000)) (hi := (262254839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649928876899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649928876899 / 500000000000) = 1/(500000000000 / 649928876899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (131127419 / 500000000) (262254839 / 1000000000) (Real.log (649928876899 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (649928876899 / 500000000000) = -Real.log (500000000000 / 649928876899) := by
    rw [show ((649928876899 / 500000000000) : ℝ) = ((500000000000 / 649928876899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (342907 / 20000000) ≤ -Real.log (983000794839 / 1000000000000) ∧
    -Real.log (983000794839 / 1000000000000) ≤ (17145351 / 1000000000) := by
  have h := checkLog_sound (w := (16999205161 / 1983000794839)) (n := 12)
    (lo := (342907 / 20000000)) (hi := (17145351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983000794839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983000794839) = 1/(983000794839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17145351 / 1000000000) (-342907 / 20000000) (Real.log (983000794839 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3412961 / 200000000) ≤ -Real.log (983079974071 / 1000000000000) ∧
    -Real.log (983079974071 / 1000000000000) ≤ (8532403 / 500000000) := by
  have h := checkLog_sound (w := (16920025929 / 1983079974071)) (n := 12)
    (lo := (3412961 / 200000000)) (hi := (8532403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983079974071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983079974071) = 1/(983079974071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8532403 / 500000000) (-3412961 / 200000000) (Real.log (983079974071 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell012
