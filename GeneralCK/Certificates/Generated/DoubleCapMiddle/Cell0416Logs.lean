import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0416
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

theorem reflection_log_1_neg : (98191197 / 500000000) ≤ -Real.log (5120 / 6231) ∧
    -Real.log (5120 / 6231) ≤ (39276479 / 200000000) := by
  have h := checkLog_sound (w := (1111 / 11351)) (n := 12)
    (lo := (98191197 / 500000000)) (hi := (39276479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6231 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6231 / 5120) = 1/(5120 / 6231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (98191197 / 500000000) (39276479 / 200000000) (Real.log (6231 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6231 / 5120) = -Real.log (5120 / 6231) := by
    rw [show ((6231 / 5120) : ℝ) = ((5120 / 6231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (48922521 / 200000000) ≤ -Real.log (4009 / 5120) ∧
    -Real.log (4009 / 5120) ≤ (122306303 / 500000000) := by
  have h := checkLog_sound (w := (1111 / 9129)) (n := 12)
    (lo := (48922521 / 200000000)) (hi := (122306303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4009) = 1/(4009 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-122306303 / 500000000) (-48922521 / 200000000) (Real.log (4009 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (196141633 / 1000000000) ≤ -Real.log (10240 / 12459) ∧
    -Real.log (10240 / 12459) ≤ (98070817 / 500000000) := by
  have h := checkLog_sound (w := (2219 / 22699)) (n := 12)
    (lo := (196141633 / 1000000000)) (hi := (98070817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12459 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12459 / 10240) = 1/(10240 / 12459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (196141633 / 1000000000) (98070817 / 500000000) (Real.log (12459 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12459 / 10240) = -Real.log (10240 / 12459) := by
    rw [show ((12459 / 10240) : ℝ) = ((10240 / 12459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (244238517 / 1000000000) ≤ -Real.log (8021 / 10240) ∧
    -Real.log (8021 / 10240) ≤ (122119259 / 500000000) := by
  have h := checkLog_sound (w := (2219 / 18261)) (n := 12)
    (lo := (244238517 / 1000000000)) (hi := (122119259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8021) = 1/(8021 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-122119259 / 500000000) (-244238517 / 1000000000) (Real.log (8021 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (180228423 / 500000000) ≤ -Real.log (2560 / 3671) ∧
    -Real.log (2560 / 3671) ≤ (360456847 / 1000000000) := by
  have h := checkLog_sound (w := (1111 / 6231)) (n := 12)
    (lo := (180228423 / 500000000)) (hi := (360456847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3671 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3671 / 2560) = 1/(2560 / 3671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (180228423 / 500000000) (360456847 / 1000000000) (Real.log (3671 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3671 / 2560) = -Real.log (2560 / 3671) := by
    rw [show ((3671 / 2560) : ℝ) = ((2560 / 3671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (113826719 / 200000000) ≤ -Real.log (1449 / 2560) ∧
    -Real.log (1449 / 2560) ≤ (142283399 / 250000000) := by
  have h := checkLog_sound (w := (1111 / 4009)) (n := 12)
    (lo := (113826719 / 200000000)) (hi := (142283399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1449) = 1/(1449 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-142283399 / 250000000) (-113826719 / 200000000) (Real.log (1449 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (180024077 / 500000000) ≤ -Real.log (5120 / 7339) ∧
    -Real.log (5120 / 7339) ≤ (72009631 / 200000000) := by
  have h := checkLog_sound (w := (2219 / 12459)) (n := 12)
    (lo := (180024077 / 500000000)) (hi := (72009631 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7339 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7339 / 5120) = 1/(5120 / 7339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (180024077 / 500000000) (72009631 / 200000000) (Real.log (7339 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7339 / 5120) = -Real.log (5120 / 7339) := by
    rw [show ((7339 / 5120) : ℝ) = ((5120 / 7339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (568098933 / 1000000000) ≤ -Real.log (2901 / 5120) ∧
    -Real.log (2901 / 5120) ≤ (284049467 / 500000000) := by
  have h := checkLog_sound (w := (2219 / 8021)) (n := 12)
    (lo := (568098933 / 1000000000)) (hi := (284049467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2901) = 1/(2901 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-284049467 / 500000000) (-568098933 / 1000000000) (Real.log (2901 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (269313141 / 1000000000) ≤ -Real.log (200000 / 261813) ∧
    -Real.log (200000 / 261813) ≤ (134656571 / 500000000) := by
  have h := checkLog_sound (w := (61813 / 461813)) (n := 12)
    (lo := (269313141 / 1000000000)) (hi := (134656571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261813 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(261813 / 200000) = 1/(200000 / 261813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (269313141 / 1000000000) (134656571 / 500000000) (Real.log (261813 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (261813 / 200000) = -Real.log (200000 / 261813) := by
    rw [show ((261813 / 200000) : ℝ) = ((200000 / 261813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (184854763 / 500000000) ≤ -Real.log (138187 / 200000) ∧
    -Real.log (138187 / 200000) ≤ (369709527 / 1000000000) := by
  have h := checkLog_sound (w := (61813 / 338187)) (n := 12)
    (lo := (184854763 / 500000000)) (hi := (369709527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 138187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 138187) = 1/(138187 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-369709527 / 1000000000) (-184854763 / 500000000) (Real.log (138187 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16852407 / 62500000) ≤ -Real.log (1000000 / 1309491) ∧
    -Real.log (1000000 / 1309491) ≤ (269638513 / 1000000000) := by
  have h := checkLog_sound (w := (309491 / 2309491)) (n := 12)
    (lo := (16852407 / 62500000)) (hi := (269638513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1309491 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1309491 / 1000000) = 1/(1000000 / 1309491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16852407 / 62500000) (269638513 / 1000000000) (Real.log (1309491 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1309491 / 1000000) = -Real.log (1000000 / 1309491) := by
    rw [show ((1309491 / 1000000) : ℝ) = ((1000000 / 1309491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1446587 / 3906250) ≤ -Real.log (690509 / 1000000) ∧
    -Real.log (690509 / 1000000) ≤ (370326273 / 1000000000) := by
  have h := checkLog_sound (w := (309491 / 1690509)) (n := 12)
    (lo := (1446587 / 3906250)) (hi := (370326273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 690509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 690509) = 1/(690509 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-370326273 / 1000000000) (-1446587 / 3906250) (Real.log (690509 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (20251463 / 100000000) ≤ -Real.log (500000 / 612239) ∧
    -Real.log (500000 / 612239) ≤ (202514631 / 1000000000) := by
  have h := checkLog_sound (w := (112239 / 1112239)) (n := 12)
    (lo := (20251463 / 100000000)) (hi := (202514631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612239 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612239 / 500000) = 1/(500000 / 612239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (20251463 / 100000000) (202514631 / 1000000000) (Real.log (612239 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (612239 / 500000) = -Real.log (500000 / 612239) := by
    rw [show ((612239 / 500000) : ℝ) = ((500000 / 612239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (254218927 / 1000000000) ≤ -Real.log (387761 / 500000) ∧
    -Real.log (387761 / 500000) ≤ (15888683 / 62500000) := by
  have h := checkLog_sound (w := (112239 / 887761)) (n := 12)
    (lo := (254218927 / 1000000000)) (hi := (15888683 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 387761) = 1/(387761 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-15888683 / 62500000) (-254218927 / 1000000000) (Real.log (387761 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (202781647 / 1000000000) ≤ -Real.log (200000 / 244961) ∧
    -Real.log (200000 / 244961) ≤ (12673853 / 62500000) := by
  have h := checkLog_sound (w := (44961 / 444961)) (n := 12)
    (lo := (202781647 / 1000000000)) (hi := (12673853 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244961 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244961 / 200000) = 1/(200000 / 244961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (202781647 / 1000000000) (12673853 / 62500000) (Real.log (244961 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (244961 / 200000) = -Real.log (200000 / 244961) := by
    rw [show ((244961 / 200000) : ℝ) = ((200000 / 244961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (63660167 / 250000000) ≤ -Real.log (155039 / 200000) ∧
    -Real.log (155039 / 200000) ≤ (254640669 / 1000000000) := by
  have h := checkLog_sound (w := (44961 / 355039)) (n := 12)
    (lo := (63660167 / 250000000)) (hi := (254640669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 155039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 155039) = 1/(155039 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-254640669 / 1000000000) (-63660167 / 250000000) (Real.log (155039 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (159755667 / 250000000) ≤ -Real.log (125000000000 / 236828536693) ∧
    -Real.log (125000000000 / 236828536693) ≤ (639022669 / 1000000000) := by
  have h := checkLog_sound (w := (111828536693 / 361828536693)) (n := 12)
    (lo := (159755667 / 250000000)) (hi := (639022669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236828536693 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236828536693 / 125000000000) = 1/(125000000000 / 236828536693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (159755667 / 250000000) (639022669 / 1000000000) (Real.log (236828536693 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (236828536693 / 125000000000) = -Real.log (125000000000 / 236828536693) := by
    rw [show ((236828536693 / 125000000000) : ℝ) = ((125000000000 / 236828536693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (39997799 / 62500000) ≤ -Real.log (250000000000 / 474103523633) ∧
    -Real.log (250000000000 / 474103523633) ≤ (127992957 / 200000000) := by
  have h := checkLog_sound (w := (224103523633 / 724103523633)) (n := 12)
    (lo := (39997799 / 62500000)) (hi := (127992957 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((474103523633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(474103523633 / 250000000000) = 1/(250000000000 / 474103523633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (39997799 / 62500000) (127992957 / 200000000) (Real.log (474103523633 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (474103523633 / 250000000000) = -Real.log (250000000000 / 474103523633) := by
    rw [show ((474103523633 / 250000000000) : ℝ) = ((250000000000 / 474103523633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (228366779 / 500000000) ≤ -Real.log (100000000000 / 157890814187) ∧
    -Real.log (100000000000 / 157890814187) ≤ (456733559 / 1000000000) := by
  have h := checkLog_sound (w := (57890814187 / 257890814187)) (n := 12)
    (lo := (228366779 / 500000000)) (hi := (456733559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157890814187 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157890814187 / 100000000000) = 1/(100000000000 / 157890814187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (228366779 / 500000000) (456733559 / 1000000000) (Real.log (157890814187 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (157890814187 / 100000000000) = -Real.log (100000000000 / 157890814187) := by
    rw [show ((157890814187 / 100000000000) : ℝ) = ((100000000000 / 157890814187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (114355579 / 250000000) ≤ -Real.log (62500000000 / 98749750063) ∧
    -Real.log (62500000000 / 98749750063) ≤ (457422317 / 1000000000) := by
  have h := checkLog_sound (w := (36249750063 / 161249750063)) (n := 12)
    (lo := (114355579 / 250000000)) (hi := (457422317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98749750063 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98749750063 / 62500000000) = 1/(62500000000 / 98749750063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (114355579 / 250000000) (457422317 / 1000000000) (Real.log (98749750063 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (98749750063 / 62500000000) = -Real.log (62500000000 / 98749750063) := by
    rw [show ((98749750063 / 62500000000) : ℝ) = ((62500000000 / 98749750063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0416
