import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell108
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

theorem reflection_log_1_neg : (272974839 / 1000000000) ≤ -Real.log (5120 / 6727) ∧
    -Real.log (5120 / 6727) ≤ (6824371 / 25000000) := by
  have h := checkLog_sound (w := (1607 / 11847)) (n := 12)
    (lo := (272974839 / 1000000000)) (hi := (6824371 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6727 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6727 / 5120) = 1/(5120 / 6727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (272974839 / 1000000000) (6824371 / 25000000) (Real.log (6727 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6727 / 5120) = -Real.log (5120 / 6727) := by
    rw [show ((6727 / 5120) : ℝ) = ((5120 / 6727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (75336813 / 200000000) ≤ -Real.log (3513 / 5120) ∧
    -Real.log (3513 / 5120) ≤ (188342033 / 500000000) := by
  have h := checkLog_sound (w := (1607 / 8633)) (n := 12)
    (lo := (75336813 / 200000000)) (hi := (188342033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3513) = 1/(3513 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-188342033 / 500000000) (-75336813 / 200000000) (Real.log (3513 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (34066097 / 125000000) ≤ -Real.log (1280 / 1681) ∧
    -Real.log (1280 / 1681) ≤ (272528777 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 2961)) (n := 12)
    (lo := (34066097 / 125000000)) (hi := (272528777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1681 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1681 / 1280) = 1/(1280 / 1681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (34066097 / 125000000) (272528777 / 1000000000) (Real.log (1681 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1681 / 1280) = -Real.log (1280 / 1681) := by
    rw [show ((1681 / 1280) : ℝ) = ((1280 / 1681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (375830459 / 1000000000) ≤ -Real.log (879 / 1280) ∧
    -Real.log (879 / 1280) ≤ (18791523 / 50000000) := by
  have h := checkLog_sound (w := (401 / 2159)) (n := 12)
    (lo := (375830459 / 1000000000)) (hi := (18791523 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 879) = 1/(879 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-18791523 / 50000000) (-375830459 / 1000000000) (Real.log (879 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (50217737 / 250000000) ≤ -Real.log (1000000 / 1222467) ∧
    -Real.log (1000000 / 1222467) ≤ (200870949 / 1000000000) := by
  have h := checkLog_sound (w := (222467 / 2222467)) (n := 12)
    (lo := (50217737 / 250000000)) (hi := (200870949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1222467 / 1000000) = 1/(1000000 / 1222467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (50217737 / 250000000) (200870949 / 1000000000) (Real.log (1222467 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1222467 / 1000000) = -Real.log (1000000 / 1222467) := by
    rw [show ((1222467 / 1000000) : ℝ) = ((1000000 / 1222467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (31453649 / 125000000) ≤ -Real.log (777533 / 1000000) ∧
    -Real.log (777533 / 1000000) ≤ (251629193 / 1000000000) := by
  have h := checkLog_sound (w := (222467 / 1777533)) (n := 12)
    (lo := (31453649 / 125000000)) (hi := (251629193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 777533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 777533) = 1/(777533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-251629193 / 1000000000) (-31453649 / 125000000) (Real.log (777533 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (100607637 / 500000000) ≤ -Real.log (125000 / 152861) ∧
    -Real.log (125000 / 152861) ≤ (8048611 / 40000000) := by
  have h := checkLog_sound (w := (27861 / 277861)) (n := 12)
    (lo := (100607637 / 500000000)) (hi := (8048611 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152861 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152861 / 125000) = 1/(125000 / 152861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (100607637 / 500000000) (8048611 / 40000000) (Real.log (152861 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (152861 / 125000) = -Real.log (125000 / 152861) := by
    rw [show ((152861 / 125000) : ℝ) = ((125000 / 152861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (126085397 / 500000000) ≤ -Real.log (97139 / 125000) ∧
    -Real.log (97139 / 125000) ≤ (50434159 / 200000000) := by
  have h := checkLog_sound (w := (27861 / 222139)) (n := 12)
    (lo := (126085397 / 500000000)) (hi := (50434159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 97139) = 1/(97139 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-50434159 / 200000000) (-126085397 / 500000000) (Real.log (97139 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (29596913 / 200000000) ≤ -Real.log (200000 / 231899) ∧
    -Real.log (200000 / 231899) ≤ (73992283 / 500000000) := by
  have h := checkLog_sound (w := (31899 / 431899)) (n := 12)
    (lo := (29596913 / 200000000)) (hi := (73992283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231899 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231899 / 200000) = 1/(200000 / 231899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (29596913 / 200000000) (73992283 / 500000000) (Real.log (231899 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (231899 / 200000) = -Real.log (200000 / 231899) := by
    rw [show ((231899 / 200000) : ℝ) = ((200000 / 231899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (173752377 / 1000000000) ≤ -Real.log (168101 / 200000) ∧
    -Real.log (168101 / 200000) ≤ (86876189 / 500000000) := by
  have h := checkLog_sound (w := (31899 / 368101)) (n := 12)
    (lo := (173752377 / 1000000000)) (hi := (86876189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 168101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 168101) = 1/(168101 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-86876189 / 500000000) (-173752377 / 1000000000) (Real.log (168101 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (148252749 / 1000000000) ≤ -Real.log (500000 / 579903) ∧
    -Real.log (500000 / 579903) ≤ (593011 / 4000000) := by
  have h := checkLog_sound (w := (79903 / 1079903)) (n := 12)
    (lo := (148252749 / 1000000000)) (hi := (593011 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((579903 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(579903 / 500000) = 1/(500000 / 579903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (148252749 / 1000000000) (593011 / 4000000) (Real.log (579903 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (579903 / 500000) = -Real.log (500000 / 579903) := by
    rw [show ((579903 / 500000) : ℝ) = ((500000 / 579903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (174122461 / 1000000000) ≤ -Real.log (420097 / 500000) ∧
    -Real.log (420097 / 500000) ≤ (87061231 / 500000000) := by
  have h := checkLog_sound (w := (79903 / 920097)) (n := 12)
    (lo := (174122461 / 1000000000)) (hi := (87061231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 420097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 420097) = 1/(420097 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-87061231 / 500000000) (-174122461 / 1000000000) (Real.log (420097 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (129671847 / 200000000) ≤ -Real.log (500000000000 / 956200227531) ∧
    -Real.log (500000000000 / 956200227531) ≤ (162089809 / 250000000) := by
  have h := checkLog_sound (w := (456200227531 / 1456200227531)) (n := 12)
    (lo := (129671847 / 200000000)) (hi := (162089809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((956200227531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(956200227531 / 500000000000) = 1/(500000000000 / 956200227531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (129671847 / 200000000) (162089809 / 250000000) (Real.log (956200227531 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (956200227531 / 500000000000) = -Real.log (500000000000 / 956200227531) := by
    rw [show ((956200227531 / 500000000000) : ℝ) = ((500000000000 / 956200227531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (129931781 / 200000000) ≤ -Real.log (100000000000 / 191488756049) ∧
    -Real.log (100000000000 / 191488756049) ≤ (324829453 / 500000000) := by
  have h := checkLog_sound (w := (91488756049 / 291488756049)) (n := 12)
    (lo := (129931781 / 200000000)) (hi := (324829453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191488756049 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191488756049 / 100000000000) = 1/(100000000000 / 191488756049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (129931781 / 200000000) (324829453 / 500000000) (Real.log (191488756049 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (191488756049 / 100000000000) = -Real.log (100000000000 / 191488756049) := by
    rw [show ((191488756049 / 100000000000) : ℝ) = ((100000000000 / 191488756049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (22625007 / 50000000) ≤ -Real.log (500000000000 / 786119045751) ∧
    -Real.log (500000000000 / 786119045751) ≤ (452500141 / 1000000000) := by
  have h := checkLog_sound (w := (286119045751 / 1286119045751)) (n := 12)
    (lo := (22625007 / 50000000)) (hi := (452500141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((786119045751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(786119045751 / 500000000000) = 1/(500000000000 / 786119045751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22625007 / 50000000) (452500141 / 1000000000) (Real.log (786119045751 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (786119045751 / 500000000000) = -Real.log (500000000000 / 786119045751) := by
    rw [show ((786119045751 / 500000000000) : ℝ) = ((500000000000 / 786119045751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (453386069 / 1000000000) ≤ -Real.log (12500000000 / 19670395001) ∧
    -Real.log (12500000000 / 19670395001) ≤ (45338607 / 100000000) := by
  have h := checkLog_sound (w := (7170395001 / 32170395001)) (n := 12)
    (lo := (453386069 / 1000000000)) (hi := (45338607 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19670395001 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19670395001 / 12500000000) = 1/(12500000000 / 19670395001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (453386069 / 1000000000) (45338607 / 100000000) (Real.log (19670395001 / 12500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (19670395001 / 12500000000) = -Real.log (12500000000 / 19670395001) := by
    rw [show ((19670395001 / 12500000000) : ℝ) = ((12500000000 / 19670395001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (160868471 / 500000000) ≤ -Real.log (500000000000 / 689760917543) ∧
    -Real.log (500000000000 / 689760917543) ≤ (321736943 / 1000000000) := by
  have h := checkLog_sound (w := (189760917543 / 1189760917543)) (n := 12)
    (lo := (160868471 / 500000000)) (hi := (321736943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689760917543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689760917543 / 500000000000) = 1/(500000000000 / 689760917543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (160868471 / 500000000) (321736943 / 1000000000) (Real.log (689760917543 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (689760917543 / 500000000000) = -Real.log (500000000000 / 689760917543) := by
    rw [show ((689760917543 / 500000000000) : ℝ) = ((500000000000 / 689760917543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (322375211 / 1000000000) ≤ -Real.log (10000000000 / 13804026213) ∧
    -Real.log (10000000000 / 13804026213) ≤ (80593803 / 250000000) := by
  have h := checkLog_sound (w := (3804026213 / 23804026213)) (n := 12)
    (lo := (322375211 / 1000000000)) (hi := (80593803 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13804026213 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13804026213 / 10000000000) = 1/(10000000000 / 13804026213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (322375211 / 1000000000) (80593803 / 250000000) (Real.log (13804026213 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13804026213 / 10000000000) = -Real.log (10000000000 / 13804026213) := by
    rw [show ((13804026213 / 10000000000) : ℝ) = ((10000000000 / 13804026213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (25869711 / 1000000000) ≤ -Real.log (243615510591 / 250000000000) ∧
    -Real.log (243615510591 / 250000000000) ≤ (1616857 / 62500000) := by
  have h := checkLog_sound (w := (6384489409 / 493615510591)) (n := 12)
    (lo := (25869711 / 1000000000)) (hi := (1616857 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243615510591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243615510591) = 1/(243615510591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1616857 / 62500000) (-25869711 / 1000000000) (Real.log (243615510591 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (25767811 / 1000000000) ≤ -Real.log (38982453799 / 40000000000) ∧
    -Real.log (38982453799 / 40000000000) ≤ (6441953 / 250000000) := by
  have h := checkLog_sound (w := (1017546201 / 78982453799)) (n := 12)
    (lo := (25767811 / 1000000000)) (hi := (6441953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38982453799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38982453799) = 1/(38982453799 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6441953 / 250000000) (-25767811 / 1000000000) (Real.log (38982453799 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell108
