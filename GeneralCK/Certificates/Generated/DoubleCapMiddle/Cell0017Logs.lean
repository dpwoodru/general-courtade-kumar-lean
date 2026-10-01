import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0017
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

theorem reflection_log_1_neg : (400766587 / 1000000000) ≤ -Real.log (1280 / 1911) ∧
    -Real.log (1280 / 1911) ≤ (100191647 / 250000000) := by
  have h := checkLog_sound (w := (631 / 3191)) (n := 12)
    (lo := (400766587 / 1000000000)) (hi := (100191647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1911 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1911 / 1280) = 1/(1280 / 1911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (400766587 / 1000000000) (100191647 / 250000000) (Real.log (1911 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1911 / 1280) = -Real.log (1280 / 1911) := by
    rw [show ((1911 / 1280) : ℝ) = ((1280 / 1911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (8489783 / 12500000) ≤ -Real.log (649 / 1280) ∧
    -Real.log (649 / 1280) ≤ (679182641 / 1000000000) := by
  have h := checkLog_sound (w := (631 / 1929)) (n := 12)
    (lo := (8489783 / 12500000)) (hi := (679182641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 649) = 1/(649 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-679182641 / 1000000000) (-8489783 / 12500000) (Real.log (649 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (399981349 / 1000000000) ≤ -Real.log (2560 / 3819) ∧
    -Real.log (2560 / 3819) ≤ (7999627 / 20000000) := by
  have h := checkLog_sound (w := (1259 / 6379)) (n := 12)
    (lo := (399981349 / 1000000000)) (hi := (7999627 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3819 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3819 / 2560) = 1/(2560 / 3819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (399981349 / 1000000000) (7999627 / 20000000) (Real.log (3819 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3819 / 2560) = -Real.log (2560 / 3819) := by
    rw [show ((3819 / 2560) : ℝ) = ((2560 / 3819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (338437029 / 500000000) ≤ -Real.log (1301 / 2560) ∧
    -Real.log (1301 / 2560) ≤ (676874059 / 1000000000) := by
  have h := checkLog_sound (w := (1259 / 3861)) (n := 12)
    (lo := (338437029 / 500000000)) (hi := (676874059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1301) = 1/(1301 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-676874059 / 1000000000) (-338437029 / 500000000) (Real.log (1301 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (343045547 / 500000000) ≤ -Real.log (640 / 1271) ∧
    -Real.log (640 / 1271) ≤ (137218219 / 200000000) := by
  have h := checkLog_sound (w := (631 / 1911)) (n := 12)
    (lo := (343045547 / 500000000)) (hi := (137218219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1271 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1271 / 640) = 1/(640 / 1271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (343045547 / 500000000) (137218219 / 200000000) (Real.log (1271 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1271 / 640) = -Real.log (640 / 1271) := by
    rw [show ((1271 / 640) : ℝ) = ((640 / 1271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (852848719 / 200000000) ≤ -Real.log (9 / 640) ∧
    -Real.log (9 / 640) ≤ (2132121801 / 500000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10 / 9) = 1/(9 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2132121801 / 500000000) (-852848719 / 200000000) (Real.log (9 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (42806889 / 62500000) ≤ -Real.log (1280 / 2539) ∧
    -Real.log (1280 / 2539) ≤ (27396409 / 40000000) := by
  have h := checkLog_sound (w := (1259 / 3819)) (n := 12)
    (lo := (42806889 / 62500000)) (hi := (27396409 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2539 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2539 / 1280) = 1/(1280 / 2539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (42806889 / 62500000) (27396409 / 40000000) (Real.log (2539 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2539 / 1280) = -Real.log (1280 / 2539) := by
    rw [show ((2539 / 1280) : ℝ) = ((1280 / 2539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1027523229 / 250000000) ≤ -Real.log (21 / 1280) ∧
    -Real.log (21 / 1280) ≤ (2055046461 / 500000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 21) = 1/(21 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2055046461 / 500000000) (-1027523229 / 250000000) (Real.log (21 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (281672413 / 500000000) ≤ -Real.log (500000 / 878269) ∧
    -Real.log (500000 / 878269) ≤ (563344827 / 1000000000) := by
  have h := checkLog_sound (w := (378269 / 1378269)) (n := 12)
    (lo := (281672413 / 500000000)) (hi := (563344827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((878269 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(878269 / 500000) = 1/(500000 / 878269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (281672413 / 500000000) (563344827 / 1000000000) (Real.log (878269 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (878269 / 500000) = -Real.log (500000 / 878269) := by
    rw [show ((878269 / 500000) : ℝ) = ((500000 / 878269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (282558881 / 200000000) ≤ -Real.log (121731 / 500000) ∧
    -Real.log (121731 / 500000) ≤ (176599301 / 125000000) := by
  have h := checkLog_sound (w := (3269 / 246731)) (n := 12)
    (lo := (5300009 / 200000000)) (hi := (13250023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 121731) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 121731) = 1/(121731 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-176599301 / 125000000) (-282558881 / 200000000) (Real.log (121731 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17655721 / 31250000) ≤ -Real.log (500000 / 879709) ∧
    -Real.log (500000 / 879709) ≤ (564983073 / 1000000000) := by
  have h := checkLog_sound (w := (379709 / 1379709)) (n := 12)
    (lo := (17655721 / 31250000)) (hi := (564983073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879709 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879709 / 500000) = 1/(500000 / 879709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17655721 / 31250000) (564983073 / 1000000000) (Real.log (879709 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (879709 / 500000) = -Real.log (500000 / 879709) := by
    rw [show ((879709 / 500000) : ℝ) = ((500000 / 879709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (142469429 / 100000000) ≤ -Real.log (120291 / 500000) ∧
    -Real.log (120291 / 500000) ≤ (1424694293 / 1000000000) := by
  have h := checkLog_sound (w := (4709 / 245291)) (n := 12)
    (lo := (3839993 / 100000000)) (hi := (38399931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 120291) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 120291) = 1/(120291 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1424694293 / 1000000000) (-142469429 / 100000000) (Real.log (120291 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (490404117 / 1000000000) ≤ -Real.log (62500 / 102061) ∧
    -Real.log (62500 / 102061) ≤ (245202059 / 500000000) := by
  have h := checkLog_sound (w := (39561 / 164561)) (n := 12)
    (lo := (490404117 / 1000000000)) (hi := (245202059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102061 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102061 / 62500) = 1/(62500 / 102061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (490404117 / 1000000000) (245202059 / 500000000) (Real.log (102061 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (102061 / 62500) = -Real.log (62500 / 102061) := by
    rw [show ((102061 / 62500) : ℝ) = ((62500 / 102061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1002328037 / 1000000000) ≤ -Real.log (22939 / 62500) ∧
    -Real.log (22939 / 62500) ≤ (1002328039 / 1000000000) := by
  have h := checkLog_sound (w := (8311 / 54189)) (n := 12)
    (lo := (309180857 / 1000000000)) (hi := (154590429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22939) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 22939) = 1/(22939 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1002328039 / 1000000000) (-1002328037 / 1000000000) (Real.log (22939 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (246184267 / 500000000) ≤ -Real.log (1000000 / 1636187) ∧
    -Real.log (1000000 / 1636187) ≤ (98473707 / 200000000) := by
  have h := checkLog_sound (w := (636187 / 2636187)) (n := 12)
    (lo := (246184267 / 500000000)) (hi := (98473707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1636187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1636187 / 1000000) = 1/(1000000 / 1636187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (246184267 / 500000000) (98473707 / 200000000) (Real.log (1636187 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1636187 / 1000000) = -Real.log (1000000 / 1636187) := by
    rw [show ((1636187 / 1000000) : ℝ) = ((1000000 / 1636187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1011115279 / 1000000000) ≤ -Real.log (363813 / 1000000) ∧
    -Real.log (363813 / 1000000) ≤ (1011115281 / 1000000000) := by
  have h := checkLog_sound (w := (136187 / 863813)) (n := 12)
    (lo := (317968099 / 1000000000)) (hi := (3179681 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 363813) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 363813) = 1/(363813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1011115281 / 1000000000) (-1011115279 / 1000000000) (Real.log (363813 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1976139231 / 1000000000) ≤ -Real.log (125000000000 / 901854293483) ∧
    -Real.log (125000000000 / 901854293483) ≤ (988069617 / 500000000) := by
  have h := checkLog_sound (w := (401854293483 / 1401854293483)) (n := 12)
    (lo := (589844871 / 1000000000)) (hi := (73730609 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((901854293483 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(901854293483 / 500000000000) = 1/(125000000000 / 901854293483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1976139231 / 1000000000) (988069617 / 500000000) (Real.log (901854293483 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (901854293483 / 125000000000) = -Real.log (125000000000 / 901854293483) := by
    rw [show ((901854293483 / 125000000000) : ℝ) = ((125000000000 / 901854293483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (994838681 / 500000000) ≤ -Real.log (50000000000 / 365658694333) ∧
    -Real.log (50000000000 / 365658694333) ≤ (397935473 / 200000000) := by
  have h := checkLog_sound (w := (165658694333 / 565658694333)) (n := 12)
    (lo := (301691501 / 500000000)) (hi := (603383003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365658694333 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(365658694333 / 200000000000) = 1/(50000000000 / 365658694333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (994838681 / 500000000) (397935473 / 200000000) (Real.log (365658694333 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (365658694333 / 50000000000) = -Real.log (50000000000 / 365658694333) := by
    rw [show ((365658694333 / 50000000000) : ℝ) = ((50000000000 / 365658694333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1492732153 / 1000000000) ≤ -Real.log (125000000000 / 556154365927) ∧
    -Real.log (125000000000 / 556154365927) ≤ (373183039 / 250000000) := by
  have h := checkLog_sound (w := (56154365927 / 1056154365927)) (n := 12)
    (lo := (106437793 / 1000000000)) (hi := (53218897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556154365927 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(556154365927 / 500000000000) = 1/(125000000000 / 556154365927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1492732153 / 1000000000) (373183039 / 250000000) (Real.log (556154365927 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (556154365927 / 125000000000) = -Real.log (125000000000 / 556154365927) := by
    rw [show ((556154365927 / 125000000000) : ℝ) = ((125000000000 / 556154365927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1503483813 / 1000000000) ≤ -Real.log (62500000000 / 281083104507) ∧
    -Real.log (62500000000 / 281083104507) ≤ (187935477 / 125000000) := by
  have h := checkLog_sound (w := (31083104507 / 531083104507)) (n := 12)
    (lo := (117189453 / 1000000000)) (hi := (58594727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281083104507 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(281083104507 / 250000000000) = 1/(62500000000 / 281083104507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1503483813 / 1000000000) (187935477 / 125000000) (Real.log (281083104507 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (281083104507 / 62500000000) = -Real.log (62500000000 / 281083104507) := by
    rw [show ((281083104507 / 62500000000) : ℝ) = ((62500000000 / 281083104507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0017
