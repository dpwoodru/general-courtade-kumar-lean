import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0372
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

theorem reflection_log_1_neg : (20691889 / 100000000) ≤ -Real.log (5120 / 6297) ∧
    -Real.log (5120 / 6297) ≤ (206918891 / 1000000000) := by
  have h := checkLog_sound (w := (1177 / 11417)) (n := 12)
    (lo := (20691889 / 100000000)) (hi := (206918891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6297 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6297 / 5120) = 1/(5120 / 6297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (20691889 / 100000000) (206918891 / 1000000000) (Real.log (6297 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6297 / 5120) = -Real.log (5120 / 6297) := by
    rw [show ((6297 / 5120) : ℝ) = ((5120 / 6297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (32651573 / 125000000) ≤ -Real.log (3943 / 5120) ∧
    -Real.log (3943 / 5120) ≤ (52242517 / 200000000) := by
  have h := checkLog_sound (w := (1177 / 9063)) (n := 12)
    (lo := (32651573 / 125000000)) (hi := (52242517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3943) = 1/(3943 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-52242517 / 200000000) (-32651573 / 125000000) (Real.log (3943 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (206680653 / 1000000000) ≤ -Real.log (10240 / 12591) ∧
    -Real.log (10240 / 12591) ≤ (103340327 / 500000000) := by
  have h := checkLog_sound (w := (2351 / 22831)) (n := 12)
    (lo := (206680653 / 1000000000)) (hi := (103340327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12591 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12591 / 10240) = 1/(10240 / 12591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (206680653 / 1000000000) (103340327 / 500000000) (Real.log (12591 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12591 / 10240) = -Real.log (10240 / 12591) := by
    rw [show ((12591 / 10240) : ℝ) = ((10240 / 12591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (52166447 / 200000000) ≤ -Real.log (7889 / 10240) ∧
    -Real.log (7889 / 10240) ≤ (65208059 / 250000000) := by
  have h := checkLog_sound (w := (2351 / 18129)) (n := 12)
    (lo := (52166447 / 200000000)) (hi := (65208059 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7889) = 1/(7889 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65208059 / 250000000) (-52166447 / 200000000) (Real.log (7889 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (94568973 / 250000000) ≤ -Real.log (2560 / 3737) ∧
    -Real.log (2560 / 3737) ≤ (378275893 / 1000000000) := by
  have h := checkLog_sound (w := (1177 / 6297)) (n := 12)
    (lo := (94568973 / 250000000)) (hi := (378275893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3737 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3737 / 2560) = 1/(2560 / 3737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (94568973 / 250000000) (378275893 / 1000000000) (Real.log (3737 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3737 / 2560) = -Real.log (2560 / 3737) := by
    rw [show ((3737 / 2560) : ℝ) = ((2560 / 3737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (123150441 / 200000000) ≤ -Real.log (1383 / 2560) ∧
    -Real.log (1383 / 2560) ≤ (307876103 / 500000000) := by
  have h := checkLog_sound (w := (1177 / 3943)) (n := 12)
    (lo := (123150441 / 200000000)) (hi := (307876103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1383) = 1/(1383 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-307876103 / 500000000) (-123150441 / 200000000) (Real.log (1383 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (377874419 / 1000000000) ≤ -Real.log (5120 / 7471) ∧
    -Real.log (5120 / 7471) ≤ (18893721 / 50000000) := by
  have h := checkLog_sound (w := (2351 / 12591)) (n := 12)
    (lo := (377874419 / 1000000000)) (hi := (18893721 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7471 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7471 / 5120) = 1/(5120 / 7471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (377874419 / 1000000000) (18893721 / 50000000) (Real.log (7471 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7471 / 5120) = -Real.log (5120 / 7471) := by
    rw [show ((7471 / 5120) : ℝ) = ((5120 / 7471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (307334097 / 500000000) ≤ -Real.log (2769 / 5120) ∧
    -Real.log (2769 / 5120) ≤ (122933639 / 200000000) := by
  have h := checkLog_sound (w := (2351 / 7889)) (n := 12)
    (lo := (307334097 / 500000000)) (hi := (122933639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2769) = 1/(2769 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-122933639 / 200000000) (-307334097 / 500000000) (Real.log (2769 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (283540759 / 1000000000) ≤ -Real.log (1000000 / 1327823) ∧
    -Real.log (1000000 / 1327823) ≤ (7088519 / 25000000) := by
  have h := checkLog_sound (w := (327823 / 2327823)) (n := 12)
    (lo := (283540759 / 1000000000)) (hi := (7088519 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1327823 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1327823 / 1000000) = 1/(1000000 / 1327823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (283540759 / 1000000000) (7088519 / 25000000) (Real.log (1327823 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1327823 / 1000000) = -Real.log (1000000 / 1327823) := by
    rw [show ((1327823 / 1000000) : ℝ) = ((1000000 / 1327823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (19861679 / 50000000) ≤ -Real.log (672177 / 1000000) ∧
    -Real.log (672177 / 1000000) ≤ (397233581 / 1000000000) := by
  have h := checkLog_sound (w := (327823 / 1672177)) (n := 12)
    (lo := (19861679 / 50000000)) (hi := (397233581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 672177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 672177) = 1/(672177 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-397233581 / 1000000000) (-19861679 / 50000000) (Real.log (672177 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (283863039 / 1000000000) ≤ -Real.log (1000000 / 1328251) ∧
    -Real.log (1000000 / 1328251) ≤ (110884 / 390625) := by
  have h := checkLog_sound (w := (328251 / 2328251)) (n := 12)
    (lo := (283863039 / 1000000000)) (hi := (110884 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1328251 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1328251 / 1000000) = 1/(1000000 / 1328251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (283863039 / 1000000000) (110884 / 390625) (Real.log (1328251 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1328251 / 1000000) = -Real.log (1000000 / 1328251) := by
    rw [show ((1328251 / 1000000) : ℝ) = ((1000000 / 1328251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (9946763 / 25000000) ≤ -Real.log (671749 / 1000000) ∧
    -Real.log (671749 / 1000000) ≤ (397870521 / 1000000000) := by
  have h := checkLog_sound (w := (328251 / 1671749)) (n := 12)
    (lo := (9946763 / 25000000)) (hi := (397870521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 671749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 671749) = 1/(671749 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-397870521 / 1000000000) (-9946763 / 25000000) (Real.log (671749 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (8569343 / 40000000) ≤ -Real.log (15625 / 19358) ∧
    -Real.log (15625 / 19358) ≤ (26779197 / 125000000) := by
  have h := checkLog_sound (w := (3733 / 34983)) (n := 12)
    (lo := (8569343 / 40000000)) (hi := (26779197 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19358 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19358 / 15625) = 1/(15625 / 19358) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (8569343 / 40000000) (26779197 / 125000000) (Real.log (19358 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (19358 / 15625) = -Real.log (15625 / 19358) := by
    rw [show ((19358 / 15625) : ℝ) = ((15625 / 19358) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (27300629 / 100000000) ≤ -Real.log (11892 / 15625) ∧
    -Real.log (11892 / 15625) ≤ (273006291 / 1000000000) := by
  have h := checkLog_sound (w := (3733 / 27517)) (n := 12)
    (lo := (27300629 / 100000000)) (hi := (273006291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11892) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11892) = 1/(11892 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-273006291 / 1000000000) (-27300629 / 100000000) (Real.log (11892 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (214500709 / 1000000000) ≤ -Real.log (1000000 / 1239243) ∧
    -Real.log (1000000 / 1239243) ≤ (21450071 / 100000000) := by
  have h := checkLog_sound (w := (239243 / 2239243)) (n := 12)
    (lo := (214500709 / 1000000000)) (hi := (21450071 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239243 / 1000000) = 1/(1000000 / 1239243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (214500709 / 1000000000) (21450071 / 100000000) (Real.log (1239243 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1239243 / 1000000) = -Real.log (1000000 / 1239243) := by
    rw [show ((1239243 / 1000000) : ℝ) = ((1000000 / 1239243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (34180161 / 125000000) ≤ -Real.log (760757 / 1000000) ∧
    -Real.log (760757 / 1000000) ≤ (273441289 / 1000000000) := by
  have h := checkLog_sound (w := (239243 / 1760757)) (n := 12)
    (lo := (34180161 / 125000000)) (hi := (273441289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 760757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 760757) = 1/(760757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-273441289 / 1000000000) (-34180161 / 125000000) (Real.log (760757 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (680774339 / 1000000000) ≤ -Real.log (500000000000 / 987703387649) ∧
    -Real.log (500000000000 / 987703387649) ≤ (34038717 / 50000000) := by
  have h := checkLog_sound (w := (487703387649 / 1487703387649)) (n := 12)
    (lo := (680774339 / 1000000000)) (hi := (34038717 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987703387649 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987703387649 / 500000000000) = 1/(500000000000 / 987703387649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (680774339 / 1000000000) (34038717 / 50000000) (Real.log (987703387649 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (987703387649 / 500000000000) = -Real.log (500000000000 / 987703387649) := by
    rw [show ((987703387649 / 500000000000) : ℝ) = ((500000000000 / 987703387649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (681733559 / 1000000000) ≤ -Real.log (250000000000 / 494325633533) ∧
    -Real.log (250000000000 / 494325633533) ≤ (17043339 / 25000000) := by
  have h := checkLog_sound (w := (244325633533 / 744325633533)) (n := 12)
    (lo := (681733559 / 1000000000)) (hi := (17043339 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494325633533 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494325633533 / 250000000000) = 1/(250000000000 / 494325633533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (681733559 / 1000000000) (17043339 / 25000000) (Real.log (494325633533 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (494325633533 / 250000000000) = -Real.log (250000000000 / 494325633533) := by
    rw [show ((494325633533 / 250000000000) : ℝ) = ((250000000000 / 494325633533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (97447973 / 200000000) ≤ -Real.log (250000000000 / 406954254961) ∧
    -Real.log (250000000000 / 406954254961) ≤ (243619933 / 500000000) := by
  have h := checkLog_sound (w := (156954254961 / 656954254961)) (n := 12)
    (lo := (97447973 / 200000000)) (hi := (243619933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((406954254961 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(406954254961 / 250000000000) = 1/(250000000000 / 406954254961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (97447973 / 200000000) (243619933 / 500000000) (Real.log (406954254961 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (406954254961 / 250000000000) = -Real.log (250000000000 / 406954254961) := by
    rw [show ((406954254961 / 250000000000) : ℝ) = ((250000000000 / 406954254961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (243970999 / 500000000) ≤ -Real.log (3125000000 / 5090501139) ∧
    -Real.log (3125000000 / 5090501139) ≤ (487941999 / 1000000000) := by
  have h := checkLog_sound (w := (1965501139 / 8215501139)) (n := 12)
    (lo := (243970999 / 500000000)) (hi := (487941999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5090501139 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5090501139 / 3125000000) = 1/(3125000000 / 5090501139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (243970999 / 500000000) (487941999 / 1000000000) (Real.log (5090501139 / 3125000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5090501139 / 3125000000) = -Real.log (3125000000 / 5090501139) := by
    rw [show ((5090501139 / 3125000000) : ℝ) = ((3125000000 / 5090501139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0372
