import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0436
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

theorem reflection_log_1_neg : (19155613 / 100000000) ≤ -Real.log (5120 / 6201) ∧
    -Real.log (5120 / 6201) ≤ (191556131 / 1000000000) := by
  have h := checkLog_sound (w := (1081 / 11321)) (n := 12)
    (lo := (19155613 / 100000000)) (hi := (191556131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6201 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6201 / 5120) = 1/(5120 / 6201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (19155613 / 100000000) (191556131 / 1000000000) (Real.log (6201 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6201 / 5120) = -Real.log (5120 / 6201) := by
    rw [show ((6201 / 5120) : ℝ) = ((5120 / 6201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (118578651 / 500000000) ≤ -Real.log (4039 / 5120) ∧
    -Real.log (4039 / 5120) ≤ (237157303 / 1000000000) := by
  have h := checkLog_sound (w := (1081 / 9159)) (n := 12)
    (lo := (118578651 / 500000000)) (hi := (237157303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4039) = 1/(4039 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-237157303 / 1000000000) (-118578651 / 500000000) (Real.log (4039 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (47828551 / 250000000) ≤ -Real.log (10240 / 12399) ∧
    -Real.log (10240 / 12399) ≤ (38262841 / 200000000) := by
  have h := checkLog_sound (w := (2159 / 22639)) (n := 12)
    (lo := (47828551 / 250000000)) (hi := (38262841 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12399 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12399 / 10240) = 1/(10240 / 12399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (47828551 / 250000000) (38262841 / 200000000) (Real.log (12399 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12399 / 10240) = -Real.log (10240 / 12399) := by
    rw [show ((12399 / 10240) : ℝ) = ((10240 / 12399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (29598249 / 125000000) ≤ -Real.log (8081 / 10240) ∧
    -Real.log (8081 / 10240) ≤ (236785993 / 1000000000) := by
  have h := checkLog_sound (w := (2159 / 18321)) (n := 12)
    (lo := (29598249 / 125000000)) (hi := (236785993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8081) = 1/(8081 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-236785993 / 1000000000) (-29598249 / 125000000) (Real.log (8081 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (35225111 / 100000000) ≤ -Real.log (2560 / 3641) ∧
    -Real.log (2560 / 3641) ≤ (352251111 / 1000000000) := by
  have h := checkLog_sound (w := (1081 / 6201)) (n := 12)
    (lo := (35225111 / 100000000)) (hi := (352251111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3641 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3641 / 2560) = 1/(2560 / 3641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (35225111 / 100000000) (352251111 / 1000000000) (Real.log (3641 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3641 / 2560) = -Real.log (2560 / 3641) := by
    rw [show ((3641 / 2560) : ℝ) = ((2560 / 3641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (274320537 / 500000000) ≤ -Real.log (1479 / 2560) ∧
    -Real.log (1479 / 2560) ≤ (21945643 / 40000000) := by
  have h := checkLog_sound (w := (1081 / 4039)) (n := 12)
    (lo := (274320537 / 500000000)) (hi := (21945643 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1479) = 1/(1479 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-21945643 / 40000000) (-274320537 / 500000000) (Real.log (1479 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (351839051 / 1000000000) ≤ -Real.log (5120 / 7279) ∧
    -Real.log (5120 / 7279) ≤ (87959763 / 250000000) := by
  have h := checkLog_sound (w := (2159 / 12399)) (n := 12)
    (lo := (351839051 / 1000000000)) (hi := (87959763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7279 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7279 / 5120) = 1/(5120 / 7279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (351839051 / 1000000000) (87959763 / 250000000) (Real.log (7279 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7279 / 5120) = -Real.log (5120 / 7279) := by
    rw [show ((7279 / 5120) : ℝ) = ((5120 / 7279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (547627389 / 1000000000) ≤ -Real.log (2961 / 5120) ∧
    -Real.log (2961 / 5120) ≤ (54762739 / 100000000) := by
  have h := checkLog_sound (w := (2159 / 8081)) (n := 12)
    (lo := (547627389 / 1000000000)) (hi := (54762739 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2961) = 1/(2961 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-54762739 / 100000000) (-547627389 / 1000000000) (Real.log (2961 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (262795709 / 1000000000) ≤ -Real.log (1000000 / 1300561) ∧
    -Real.log (1000000 / 1300561) ≤ (26279571 / 100000000) := by
  have h := checkLog_sound (w := (300561 / 2300561)) (n := 12)
    (lo := (262795709 / 1000000000)) (hi := (26279571 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1300561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1300561 / 1000000) = 1/(1000000 / 1300561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (262795709 / 1000000000) (26279571 / 100000000) (Real.log (1300561 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1300561 / 1000000) = -Real.log (1000000 / 1300561) := by
    rw [show ((1300561 / 1000000) : ℝ) = ((1000000 / 1300561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (357476693 / 1000000000) ≤ -Real.log (699439 / 1000000) ∧
    -Real.log (699439 / 1000000) ≤ (178738347 / 500000000) := by
  have h := checkLog_sound (w := (300561 / 1699439)) (n := 12)
    (lo := (357476693 / 1000000000)) (hi := (178738347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 699439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 699439) = 1/(699439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-178738347 / 500000000) (-357476693 / 1000000000) (Real.log (699439 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (263123207 / 1000000000) ≤ -Real.log (1000000 / 1300987) ∧
    -Real.log (1000000 / 1300987) ≤ (32890401 / 125000000) := by
  have h := checkLog_sound (w := (300987 / 2300987)) (n := 12)
    (lo := (263123207 / 1000000000)) (hi := (32890401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1300987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1300987 / 1000000) = 1/(1000000 / 1300987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (263123207 / 1000000000) (32890401 / 125000000) (Real.log (1300987 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1300987 / 1000000) = -Real.log (1000000 / 1300987) := by
    rw [show ((1300987 / 1000000) : ℝ) = ((1000000 / 1300987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (179042969 / 500000000) ≤ -Real.log (699013 / 1000000) ∧
    -Real.log (699013 / 1000000) ≤ (358085939 / 1000000000) := by
  have h := checkLog_sound (w := (300987 / 1699013)) (n := 12)
    (lo := (179042969 / 500000000)) (hi := (358085939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 699013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 699013) = 1/(699013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-358085939 / 1000000000) (-179042969 / 500000000) (Real.log (699013 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (197194569 / 1000000000) ≤ -Real.log (1000000 / 1217981) ∧
    -Real.log (1000000 / 1217981) ≤ (19719457 / 100000000) := by
  have h := checkLog_sound (w := (217981 / 2217981)) (n := 12)
    (lo := (197194569 / 1000000000)) (hi := (19719457 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217981 / 1000000) = 1/(1000000 / 1217981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (197194569 / 1000000000) (19719457 / 100000000) (Real.log (1217981 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1217981 / 1000000) = -Real.log (1000000 / 1217981) := by
    rw [show ((1217981 / 1000000) : ℝ) = ((1000000 / 1217981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (122938121 / 500000000) ≤ -Real.log (782019 / 1000000) ∧
    -Real.log (782019 / 1000000) ≤ (245876243 / 1000000000) := by
  have h := checkLog_sound (w := (217981 / 1782019)) (n := 12)
    (lo := (122938121 / 500000000)) (hi := (245876243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782019) = 1/(782019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-245876243 / 1000000000) (-122938121 / 500000000) (Real.log (782019 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (197461369 / 1000000000) ≤ -Real.log (500000 / 609153) ∧
    -Real.log (500000 / 609153) ≤ (19746137 / 100000000) := by
  have h := checkLog_sound (w := (109153 / 1109153)) (n := 12)
    (lo := (197461369 / 1000000000)) (hi := (19746137 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609153 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609153 / 500000) = 1/(500000 / 609153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (197461369 / 1000000000) (19746137 / 100000000) (Real.log (609153 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (609153 / 500000) = -Real.log (500000 / 609153) := by
    rw [show ((609153 / 500000) : ℝ) = ((500000 / 609153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (246291919 / 1000000000) ≤ -Real.log (390847 / 500000) ∧
    -Real.log (390847 / 500000) ≤ (3078649 / 12500000) := by
  have h := checkLog_sound (w := (109153 / 890847)) (n := 12)
    (lo := (246291919 / 1000000000)) (hi := (3078649 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 390847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 390847) = 1/(390847 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3078649 / 12500000) (-246291919 / 1000000000) (Real.log (390847 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (620272403 / 1000000000) ≤ -Real.log (25000000000 / 46485862241) ∧
    -Real.log (25000000000 / 46485862241) ≤ (155068101 / 250000000) := by
  have h := checkLog_sound (w := (21485862241 / 71485862241)) (n := 12)
    (lo := (620272403 / 1000000000)) (hi := (155068101 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46485862241 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46485862241 / 25000000000) = 1/(25000000000 / 46485862241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (620272403 / 1000000000) (155068101 / 250000000) (Real.log (46485862241 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (46485862241 / 25000000000) = -Real.log (25000000000 / 46485862241) := by
    rw [show ((46485862241 / 25000000000) : ℝ) = ((25000000000 / 46485862241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (310604573 / 500000000) ≤ -Real.log (500000000000 / 930588558439) ∧
    -Real.log (500000000000 / 930588558439) ≤ (621209147 / 1000000000) := by
  have h := checkLog_sound (w := (430588558439 / 1430588558439)) (n := 12)
    (lo := (310604573 / 500000000)) (hi := (621209147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((930588558439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(930588558439 / 500000000000) = 1/(500000000000 / 930588558439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (310604573 / 500000000) (621209147 / 1000000000) (Real.log (930588558439 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (930588558439 / 500000000000) = -Real.log (500000000000 / 930588558439) := by
    rw [show ((930588558439 / 500000000000) : ℝ) = ((500000000000 / 930588558439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (443070811 / 1000000000) ≤ -Real.log (250000000000 / 389370654677) ∧
    -Real.log (250000000000 / 389370654677) ≤ (110767703 / 250000000) := by
  have h := checkLog_sound (w := (139370654677 / 639370654677)) (n := 12)
    (lo := (443070811 / 1000000000)) (hi := (110767703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((389370654677 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(389370654677 / 250000000000) = 1/(250000000000 / 389370654677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (443070811 / 1000000000) (110767703 / 250000000) (Real.log (389370654677 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (389370654677 / 250000000000) = -Real.log (250000000000 / 389370654677) := by
    rw [show ((389370654677 / 250000000000) : ℝ) = ((250000000000 / 389370654677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (55469161 / 125000000) ≤ -Real.log (50000000000 / 77927296359) ∧
    -Real.log (50000000000 / 77927296359) ≤ (443753289 / 1000000000) := by
  have h := checkLog_sound (w := (27927296359 / 127927296359)) (n := 12)
    (lo := (55469161 / 125000000)) (hi := (443753289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77927296359 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77927296359 / 50000000000) = 1/(50000000000 / 77927296359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (55469161 / 125000000) (443753289 / 1000000000) (Real.log (77927296359 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (77927296359 / 50000000000) = -Real.log (50000000000 / 77927296359) := by
    rw [show ((77927296359 / 50000000000) : ℝ) = ((50000000000 / 77927296359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0436
