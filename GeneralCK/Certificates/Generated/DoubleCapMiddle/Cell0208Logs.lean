import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0208
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

theorem reflection_log_1_neg : (131031869 / 500000000) ≤ -Real.log (2560 / 3327) ∧
    -Real.log (2560 / 3327) ≤ (262063739 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 5887)) (n := 12)
    (lo := (131031869 / 500000000)) (hi := (262063739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3327 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3327 / 2560) = 1/(2560 / 3327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (131031869 / 500000000) (262063739 / 1000000000) (Real.log (3327 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3327 / 2560) = -Real.log (2560 / 3327) := by
    rw [show ((3327 / 2560) : ℝ) = ((2560 / 3327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (356117063 / 1000000000) ≤ -Real.log (1793 / 2560) ∧
    -Real.log (1793 / 2560) ≤ (44514633 / 125000000) := by
  have h := checkLog_sound (w := (767 / 4353)) (n := 12)
    (lo := (356117063 / 1000000000)) (hi := (44514633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1793) = 1/(1793 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-44514633 / 125000000) (-356117063 / 1000000000) (Real.log (1793 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13080639 / 50000000) ≤ -Real.log (5120 / 6651) ∧
    -Real.log (5120 / 6651) ≤ (261612781 / 1000000000) := by
  have h := checkLog_sound (w := (1531 / 11771)) (n := 12)
    (lo := (13080639 / 50000000)) (hi := (261612781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6651 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6651 / 5120) = 1/(5120 / 6651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13080639 / 50000000) (261612781 / 1000000000) (Real.log (6651 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6651 / 5120) = -Real.log (5120 / 6651) := by
    rw [show ((6651 / 5120) : ℝ) = ((5120 / 6651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (177640413 / 500000000) ≤ -Real.log (3589 / 5120) ∧
    -Real.log (3589 / 5120) ≤ (355280827 / 1000000000) := by
  have h := checkLog_sound (w := (1531 / 8709)) (n := 12)
    (lo := (177640413 / 500000000)) (hi := (355280827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3589) = 1/(3589 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-355280827 / 1000000000) (-177640413 / 500000000) (Real.log (3589 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (117378807 / 250000000) ≤ -Real.log (1280 / 2047) ∧
    -Real.log (1280 / 2047) ≤ (469515229 / 1000000000) := by
  have h := checkLog_sound (w := (767 / 3327)) (n := 12)
    (lo := (117378807 / 250000000)) (hi := (469515229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2047 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2047 / 1280) = 1/(1280 / 2047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (117378807 / 250000000) (469515229 / 1000000000) (Real.log (2047 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2047 / 1280) = -Real.log (1280 / 2047) := by
    rw [show ((2047 / 1280) : ℝ) = ((1280 / 2047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (914339511 / 1000000000) ≤ -Real.log (513 / 1280) ∧
    -Real.log (513 / 1280) ≤ (914339513 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 1153)) (n := 12)
    (lo := (221192331 / 1000000000)) (hi := (55298083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 513) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 513) = 1/(513 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-914339513 / 1000000000) (-914339511 / 1000000000) (Real.log (513 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23439109 / 50000000) ≤ -Real.log (2560 / 4091) ∧
    -Real.log (2560 / 4091) ≤ (468782181 / 1000000000) := by
  have h := checkLog_sound (w := (1531 / 6651)) (n := 12)
    (lo := (23439109 / 50000000)) (hi := (468782181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4091 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4091 / 2560) = 1/(2560 / 4091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23439109 / 50000000) (468782181 / 1000000000) (Real.log (4091 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4091 / 2560) = -Real.log (2560 / 4091) := by
    rw [show ((4091 / 2560) : ℝ) = ((2560 / 4091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (911419801 / 1000000000) ≤ -Real.log (1029 / 2560) ∧
    -Real.log (1029 / 2560) ≤ (911419803 / 1000000000) := by
  have h := checkLog_sound (w := (251 / 2309)) (n := 12)
    (lo := (218272621 / 1000000000)) (hi := (109136311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1029) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1029) = 1/(1029 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-911419803 / 1000000000) (-911419801 / 1000000000) (Real.log (1029 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (71584533 / 200000000) ≤ -Real.log (200000 / 286071) ∧
    -Real.log (200000 / 286071) ≤ (178961333 / 500000000) := by
  have h := checkLog_sound (w := (86071 / 486071)) (n := 12)
    (lo := (71584533 / 200000000)) (hi := (178961333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286071 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(286071 / 200000) = 1/(200000 / 286071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (71584533 / 200000000) (178961333 / 500000000) (Real.log (286071 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (286071 / 200000) = -Real.log (200000 / 286071) := by
    rw [show ((286071 / 200000) : ℝ) = ((200000 / 286071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (562741919 / 1000000000) ≤ -Real.log (113929 / 200000) ∧
    -Real.log (113929 / 200000) ≤ (3517137 / 6250000) := by
  have h := checkLog_sound (w := (86071 / 313929)) (n := 12)
    (lo := (562741919 / 1000000000)) (hi := (3517137 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 113929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 113929) = 1/(113929 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3517137 / 6250000) (-562741919 / 1000000000) (Real.log (113929 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (358537707 / 1000000000) ≤ -Real.log (200000 / 286247) ∧
    -Real.log (200000 / 286247) ≤ (89634427 / 250000000) := by
  have h := checkLog_sound (w := (86247 / 486247)) (n := 12)
    (lo := (358537707 / 1000000000)) (hi := (89634427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286247 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(286247 / 200000) = 1/(200000 / 286247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (358537707 / 1000000000) (89634427 / 250000000) (Real.log (286247 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (286247 / 200000) = -Real.log (200000 / 286247) := by
    rw [show ((286247 / 200000) : ℝ) = ((200000 / 286247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (112857587 / 200000000) ≤ -Real.log (113753 / 200000) ∧
    -Real.log (113753 / 200000) ≤ (8816999 / 15625000) := by
  have h := checkLog_sound (w := (86247 / 313753)) (n := 12)
    (lo := (112857587 / 200000000)) (hi := (8816999 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 113753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 113753) = 1/(113753 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-8816999 / 15625000) (-112857587 / 200000000) (Real.log (113753 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (34771941 / 125000000) ≤ -Real.log (500000 / 660359) ∧
    -Real.log (500000 / 660359) ≤ (278175529 / 1000000000) := by
  have h := checkLog_sound (w := (160359 / 1160359)) (n := 12)
    (lo := (34771941 / 125000000)) (hi := (278175529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660359 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660359 / 500000) = 1/(500000 / 660359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (34771941 / 125000000) (278175529 / 1000000000) (Real.log (660359 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (660359 / 500000) = -Real.log (500000 / 660359) := by
    rw [show ((660359 / 500000) : ℝ) = ((500000 / 660359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (386718921 / 1000000000) ≤ -Real.log (339641 / 500000) ∧
    -Real.log (339641 / 500000) ≤ (193359461 / 500000000) := by
  have h := checkLog_sound (w := (160359 / 839641)) (n := 12)
    (lo := (386718921 / 1000000000)) (hi := (193359461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 339641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 339641) = 1/(339641 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-193359461 / 500000000) (-386718921 / 1000000000) (Real.log (339641 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (139362539 / 500000000) ≤ -Real.log (250000 / 330361) ∧
    -Real.log (250000 / 330361) ≤ (278725079 / 1000000000) := by
  have h := checkLog_sound (w := (80361 / 580361)) (n := 12)
    (lo := (139362539 / 500000000)) (hi := (278725079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330361 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330361 / 250000) = 1/(250000 / 330361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (139362539 / 500000000) (278725079 / 1000000000) (Real.log (330361 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (330361 / 250000) = -Real.log (250000 / 330361) := by
    rw [show ((330361 / 250000) : ℝ) = ((250000 / 330361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (96947067 / 250000000) ≤ -Real.log (169639 / 250000) ∧
    -Real.log (169639 / 250000) ≤ (387788269 / 1000000000) := by
  have h := checkLog_sound (w := (80361 / 419639)) (n := 12)
    (lo := (96947067 / 250000000)) (hi := (387788269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 169639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 169639) = 1/(169639 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-387788269 / 1000000000) (-96947067 / 250000000) (Real.log (169639 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (920664583 / 1000000000) ≤ -Real.log (500000000000 / 1255479289733) ∧
    -Real.log (500000000000 / 1255479289733) ≤ (184132917 / 200000000) := by
  have h := checkLog_sound (w := (255479289733 / 2255479289733)) (n := 12)
    (lo := (227517403 / 1000000000)) (hi := (56879351 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1255479289733 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1255479289733 / 1000000000000) = 1/(500000000000 / 1255479289733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (920664583 / 1000000000) (184132917 / 200000000) (Real.log (1255479289733 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1255479289733 / 500000000000) = -Real.log (500000000000 / 1255479289733) := by
    rw [show ((1255479289733 / 500000000000) : ℝ) = ((500000000000 / 1255479289733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (461412821 / 500000000) ≤ -Real.log (250000000000 / 629097694127) ∧
    -Real.log (250000000000 / 629097694127) ≤ (230706411 / 250000000) := by
  have h := checkLog_sound (w := (129097694127 / 1129097694127)) (n := 12)
    (lo := (114839231 / 500000000)) (hi := (229678463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629097694127 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(629097694127 / 500000000000) = 1/(250000000000 / 629097694127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (461412821 / 500000000) (230706411 / 250000000) (Real.log (629097694127 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (629097694127 / 250000000000) = -Real.log (250000000000 / 629097694127) := by
    rw [show ((629097694127 / 250000000000) : ℝ) = ((250000000000 / 629097694127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (664894449 / 1000000000) ≤ -Real.log (500000000000 / 972142644733) ∧
    -Real.log (500000000000 / 972142644733) ≤ (13297889 / 20000000) := by
  have h := checkLog_sound (w := (472142644733 / 1472142644733)) (n := 12)
    (lo := (664894449 / 1000000000)) (hi := (13297889 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972142644733 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972142644733 / 500000000000) = 1/(500000000000 / 972142644733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (664894449 / 1000000000) (13297889 / 20000000) (Real.log (972142644733 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (972142644733 / 500000000000) = -Real.log (500000000000 / 972142644733) := by
    rw [show ((972142644733 / 500000000000) : ℝ) = ((500000000000 / 972142644733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (333256673 / 500000000) ≤ -Real.log (250000000000 / 486858859107) ∧
    -Real.log (250000000000 / 486858859107) ≤ (666513347 / 1000000000) := by
  have h := checkLog_sound (w := (236858859107 / 736858859107)) (n := 12)
    (lo := (333256673 / 500000000)) (hi := (666513347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((486858859107 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(486858859107 / 250000000000) = 1/(250000000000 / 486858859107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (333256673 / 500000000) (666513347 / 1000000000) (Real.log (486858859107 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (486858859107 / 250000000000) = -Real.log (250000000000 / 486858859107) := by
    rw [show ((486858859107 / 250000000000) : ℝ) = ((250000000000 / 486858859107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0208
