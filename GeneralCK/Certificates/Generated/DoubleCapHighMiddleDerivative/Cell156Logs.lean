import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell156
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

theorem reflection_log_1_neg : (18384701 / 62500000) ≤ -Real.log (5120 / 6871) ∧
    -Real.log (5120 / 6871) ≤ (294155217 / 1000000000) := by
  have h := checkLog_sound (w := (1751 / 11991)) (n := 12)
    (lo := (18384701 / 62500000)) (hi := (294155217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6871 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6871 / 5120) = 1/(5120 / 6871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (18384701 / 62500000) (294155217 / 1000000000) (Real.log (6871 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6871 / 5120) = -Real.log (5120 / 6871) := by
    rw [show ((6871 / 5120) : ℝ) = ((5120 / 6871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (209269237 / 500000000) ≤ -Real.log (3369 / 5120) ∧
    -Real.log (3369 / 5120) ≤ (16741539 / 40000000) := by
  have h := checkLog_sound (w := (1751 / 8489)) (n := 12)
    (lo := (209269237 / 500000000)) (hi := (16741539 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3369) = 1/(3369 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-16741539 / 40000000) (-209269237 / 500000000) (Real.log (3369 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (293718503 / 1000000000) ≤ -Real.log (1280 / 1717) ∧
    -Real.log (1280 / 1717) ≤ (36714813 / 125000000) := by
  have h := checkLog_sound (w := (437 / 2997)) (n := 12)
    (lo := (293718503 / 1000000000)) (hi := (36714813 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1717 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1717 / 1280) = 1/(1280 / 1717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (293718503 / 1000000000) (36714813 / 125000000) (Real.log (1717 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1717 / 1280) = -Real.log (1280 / 1717) := by
    rw [show ((1717 / 1280) : ℝ) = ((1280 / 1717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (208824199 / 500000000) ≤ -Real.log (843 / 1280) ∧
    -Real.log (843 / 1280) ≤ (417648399 / 1000000000) := by
  have h := checkLog_sound (w := (437 / 2123)) (n := 12)
    (lo := (208824199 / 500000000)) (hi := (417648399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 843) = 1/(843 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-417648399 / 1000000000) (-208824199 / 500000000) (Real.log (843 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (108620281 / 500000000) ≤ -Real.log (1000000 / 1242643) ∧
    -Real.log (1000000 / 1242643) ≤ (217240563 / 1000000000) := by
  have h := checkLog_sound (w := (242643 / 2242643)) (n := 12)
    (lo := (108620281 / 500000000)) (hi := (217240563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1242643 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1242643 / 1000000) = 1/(1000000 / 1242643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (108620281 / 500000000) (217240563 / 1000000000) (Real.log (1242643 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1242643 / 1000000) = -Real.log (1000000 / 1242643) := by
    rw [show ((1242643 / 1000000) : ℝ) = ((1000000 / 1242643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (138960269 / 500000000) ≤ -Real.log (757357 / 1000000) ∧
    -Real.log (757357 / 1000000) ≤ (277920539 / 1000000000) := by
  have h := checkLog_sound (w := (242643 / 1757357)) (n := 12)
    (lo := (138960269 / 500000000)) (hi := (277920539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 757357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 757357) = 1/(757357 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-277920539 / 1000000000) (-138960269 / 500000000) (Real.log (757357 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (27197513 / 125000000) ≤ -Real.log (200000 / 248613) ∧
    -Real.log (200000 / 248613) ≤ (43516021 / 200000000) := by
  have h := checkLog_sound (w := (48613 / 448613)) (n := 12)
    (lo := (27197513 / 125000000)) (hi := (43516021 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248613 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248613 / 200000) = 1/(200000 / 248613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (27197513 / 125000000) (43516021 / 200000000) (Real.log (248613 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (248613 / 200000) = -Real.log (200000 / 248613) := by
    rw [show ((248613 / 200000) : ℝ) = ((200000 / 248613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (139238947 / 500000000) ≤ -Real.log (151387 / 200000) ∧
    -Real.log (151387 / 200000) ≤ (55695579 / 200000000) := by
  have h := checkLog_sound (w := (48613 / 351387)) (n := 12)
    (lo := (139238947 / 500000000)) (hi := (55695579 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 151387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 151387) = 1/(151387 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-55695579 / 200000000) (-139238947 / 500000000) (Real.log (151387 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (160773557 / 1000000000) ≤ -Real.log (1000000 / 1174419) ∧
    -Real.log (1000000 / 1174419) ≤ (80386779 / 500000000) := by
  have h := checkLog_sound (w := (174419 / 2174419)) (n := 12)
    (lo := (160773557 / 1000000000)) (hi := (80386779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1174419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1174419 / 1000000) = 1/(1000000 / 1174419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (160773557 / 1000000000) (80386779 / 500000000) (Real.log (1174419 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1174419 / 1000000) = -Real.log (1000000 / 1174419) := by
    rw [show ((1174419 / 1000000) : ℝ) = ((1000000 / 1174419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (95833949 / 500000000) ≤ -Real.log (825581 / 1000000) ∧
    -Real.log (825581 / 1000000) ≤ (191667899 / 1000000000) := by
  have h := checkLog_sound (w := (174419 / 1825581)) (n := 12)
    (lo := (95833949 / 500000000)) (hi := (191667899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 825581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 825581) = 1/(825581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-191667899 / 1000000000) (-95833949 / 500000000) (Real.log (825581 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (161040887 / 1000000000) ≤ -Real.log (1000000 / 1174733) ∧
    -Real.log (1000000 / 1174733) ≤ (20130111 / 125000000) := by
  have h := checkLog_sound (w := (174733 / 2174733)) (n := 12)
    (lo := (161040887 / 1000000000)) (hi := (20130111 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1174733 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1174733 / 1000000) = 1/(1000000 / 1174733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (161040887 / 1000000000) (20130111 / 125000000) (Real.log (1174733 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1174733 / 1000000) = -Real.log (1000000 / 1174733) := by
    rw [show ((1174733 / 1000000) : ℝ) = ((1000000 / 1174733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (48012077 / 250000000) ≤ -Real.log (825267 / 1000000) ∧
    -Real.log (825267 / 1000000) ≤ (192048309 / 1000000000) := by
  have h := checkLog_sound (w := (174733 / 1825267)) (n := 12)
    (lo := (48012077 / 250000000)) (hi := (192048309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 825267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 825267) = 1/(825267 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-192048309 / 1000000000) (-48012077 / 250000000) (Real.log (825267 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (355683451 / 500000000) ≤ -Real.log (125000000000 / 254596678529) ∧
    -Real.log (125000000000 / 254596678529) ≤ (88920863 / 125000000) := by
  have h := checkLog_sound (w := (4596678529 / 504596678529)) (n := 12)
    (lo := (9109861 / 500000000)) (hi := (18219723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((254596678529 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(254596678529 / 250000000000) = 1/(125000000000 / 254596678529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (355683451 / 500000000) (88920863 / 125000000) (Real.log (254596678529 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (254596678529 / 125000000000) = -Real.log (125000000000 / 254596678529) := by
    rw [show ((254596678529 / 125000000000) : ℝ) = ((125000000000 / 254596678529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (712693691 / 1000000000) ≤ -Real.log (100000000000 / 203947758979) ∧
    -Real.log (100000000000 / 203947758979) ≤ (712693693 / 1000000000) := by
  have h := checkLog_sound (w := (3947758979 / 403947758979)) (n := 12)
    (lo := (19546511 / 1000000000)) (hi := (1221657 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203947758979 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(203947758979 / 200000000000) = 1/(100000000000 / 203947758979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (712693691 / 1000000000) (712693693 / 1000000000) (Real.log (203947758979 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (203947758979 / 100000000000) = -Real.log (100000000000 / 203947758979) := by
    rw [show ((203947758979 / 100000000000) : ℝ) = ((100000000000 / 203947758979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (495161101 / 1000000000) ≤ -Real.log (31250000000 / 51273829581) ∧
    -Real.log (31250000000 / 51273829581) ≤ (247580551 / 500000000) := by
  have h := checkLog_sound (w := (20023829581 / 82523829581)) (n := 12)
    (lo := (495161101 / 1000000000)) (hi := (247580551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51273829581 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51273829581 / 31250000000) = 1/(31250000000 / 51273829581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (495161101 / 1000000000) (247580551 / 500000000) (Real.log (51273829581 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (51273829581 / 31250000000) = -Real.log (31250000000 / 51273829581) := by
    rw [show ((51273829581 / 31250000000) : ℝ) = ((31250000000 / 51273829581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (248028999 / 500000000) ≤ -Real.log (250000000000 / 410558700549) ∧
    -Real.log (250000000000 / 410558700549) ≤ (496057999 / 1000000000) := by
  have h := checkLog_sound (w := (160558700549 / 660558700549)) (n := 12)
    (lo := (248028999 / 500000000)) (hi := (496057999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410558700549 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410558700549 / 250000000000) = 1/(250000000000 / 410558700549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (248028999 / 500000000) (496057999 / 1000000000) (Real.log (410558700549 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (410558700549 / 250000000000) = -Real.log (250000000000 / 410558700549) := by
    rw [show ((410558700549 / 250000000000) : ℝ) = ((250000000000 / 410558700549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (70488291 / 200000000) ≤ -Real.log (500000000000 / 711268185677) ∧
    -Real.log (500000000000 / 711268185677) ≤ (22027591 / 62500000) := by
  have h := checkLog_sound (w := (211268185677 / 1211268185677)) (n := 12)
    (lo := (70488291 / 200000000)) (hi := (22027591 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711268185677 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711268185677 / 500000000000) = 1/(500000000000 / 711268185677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (70488291 / 200000000) (22027591 / 62500000) (Real.log (711268185677 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (711268185677 / 500000000000) = -Real.log (500000000000 / 711268185677) := by
    rw [show ((711268185677 / 500000000000) : ℝ) = ((500000000000 / 711268185677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (88272299 / 250000000) ≤ -Real.log (500000000000 / 711729052537) ∧
    -Real.log (500000000000 / 711729052537) ≤ (353089197 / 1000000000) := by
  have h := checkLog_sound (w := (211729052537 / 1211729052537)) (n := 12)
    (lo := (88272299 / 250000000)) (hi := (353089197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711729052537 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711729052537 / 500000000000) = 1/(500000000000 / 711729052537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (88272299 / 250000000) (353089197 / 1000000000) (Real.log (711729052537 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (711729052537 / 500000000000) = -Real.log (500000000000 / 711729052537) := by
    rw [show ((711729052537 / 500000000000) : ℝ) = ((500000000000 / 711729052537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1550371 / 50000000) ≤ -Real.log (969468378711 / 1000000000000) ∧
    -Real.log (969468378711 / 1000000000000) ≤ (31007421 / 1000000000) := by
  have h := checkLog_sound (w := (30531621289 / 1969468378711)) (n := 12)
    (lo := (1550371 / 50000000)) (hi := (31007421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969468378711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969468378711) = 1/(969468378711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-31007421 / 1000000000) (-1550371 / 50000000) (Real.log (969468378711 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1544717 / 50000000) ≤ -Real.log (969578012439 / 1000000000000) ∧
    -Real.log (969578012439 / 1000000000000) ≤ (30894341 / 1000000000) := by
  have h := checkLog_sound (w := (30421987561 / 1969578012439)) (n := 12)
    (lo := (1544717 / 50000000)) (hi := (30894341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969578012439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969578012439) = 1/(969578012439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-30894341 / 1000000000) (-1544717 / 50000000) (Real.log (969578012439 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell156
