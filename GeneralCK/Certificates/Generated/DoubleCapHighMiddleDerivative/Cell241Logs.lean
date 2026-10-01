import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell241
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

theorem reflection_log_1_neg : (82648907 / 250000000) ≤ -Real.log (2560 / 3563) ∧
    -Real.log (2560 / 3563) ≤ (330595629 / 1000000000) := by
  have h := checkLog_sound (w := (1003 / 6123)) (n := 12)
    (lo := (82648907 / 250000000)) (hi := (330595629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3563 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3563 / 2560) = 1/(2560 / 3563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (82648907 / 250000000) (330595629 / 1000000000) (Real.log (3563 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3563 / 2560) = -Real.log (2560 / 3563) := by
    rw [show ((3563 / 2560) : ℝ) = ((2560 / 3563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (99449273 / 200000000) ≤ -Real.log (1557 / 2560) ∧
    -Real.log (1557 / 2560) ≤ (248623183 / 500000000) := by
  have h := checkLog_sound (w := (1003 / 4117)) (n := 12)
    (lo := (99449273 / 200000000)) (hi := (248623183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1557) = 1/(1557 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-248623183 / 500000000) (-99449273 / 200000000) (Real.log (1557 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (66034909 / 200000000) ≤ -Real.log (5120 / 7123) ∧
    -Real.log (5120 / 7123) ≤ (165087273 / 500000000) := by
  have h := checkLog_sound (w := (2003 / 12243)) (n := 12)
    (lo := (66034909 / 200000000)) (hi := (165087273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7123 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7123 / 5120) = 1/(5120 / 7123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (66034909 / 200000000) (165087273 / 500000000) (Real.log (7123 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7123 / 5120) = -Real.log (5120 / 7123) := by
    rw [show ((7123 / 5120) : ℝ) = ((5120 / 7123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (248141719 / 500000000) ≤ -Real.log (3117 / 5120) ∧
    -Real.log (3117 / 5120) ≤ (496283439 / 1000000000) := by
  have h := checkLog_sound (w := (2003 / 8237)) (n := 12)
    (lo := (248141719 / 500000000)) (hi := (496283439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3117) = 1/(3117 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-496283439 / 1000000000) (-248141719 / 500000000) (Real.log (3117 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (245697683 / 1000000000) ≤ -Real.log (1000000 / 1278513) ∧
    -Real.log (1000000 / 1278513) ≤ (61424421 / 250000000) := by
  have h := checkLog_sound (w := (278513 / 2278513)) (n := 12)
    (lo := (245697683 / 1000000000)) (hi := (61424421 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1278513 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1278513 / 1000000) = 1/(1000000 / 1278513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (245697683 / 1000000000) (61424421 / 250000000) (Real.log (1278513 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1278513 / 1000000) = -Real.log (1000000 / 1278513) := by
    rw [show ((1278513 / 1000000) : ℝ) = ((1000000 / 1278513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (163220459 / 500000000) ≤ -Real.log (721487 / 1000000) ∧
    -Real.log (721487 / 1000000) ≤ (326440919 / 1000000000) := by
  have h := checkLog_sound (w := (278513 / 1721487)) (n := 12)
    (lo := (163220459 / 500000000)) (hi := (326440919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 721487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 721487) = 1/(721487 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-326440919 / 1000000000) (-163220459 / 500000000) (Real.log (721487 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (123015023 / 500000000) ≤ -Real.log (500000 / 639469) ∧
    -Real.log (500000 / 639469) ≤ (246030047 / 1000000000) := by
  have h := checkLog_sound (w := (139469 / 1139469)) (n := 12)
    (lo := (123015023 / 500000000)) (hi := (246030047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639469 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639469 / 500000) = 1/(500000 / 639469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (123015023 / 500000000) (246030047 / 1000000000) (Real.log (639469 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (639469 / 500000) = -Real.log (500000 / 639469) := by
    rw [show ((639469 / 500000) : ℝ) = ((500000 / 639469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (327030153 / 1000000000) ≤ -Real.log (360531 / 500000) ∧
    -Real.log (360531 / 500000) ≤ (163515077 / 500000000) := by
  have h := checkLog_sound (w := (139469 / 860531)) (n := 12)
    (lo := (327030153 / 1000000000)) (hi := (163515077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 360531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 360531) = 1/(360531 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-163515077 / 500000000) (-327030153 / 1000000000) (Real.log (360531 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18337267 / 100000000) ≤ -Real.log (500000 / 600631) ∧
    -Real.log (500000 / 600631) ≤ (183372671 / 1000000000) := by
  have h := checkLog_sound (w := (100631 / 1100631)) (n := 12)
    (lo := (18337267 / 100000000)) (hi := (183372671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600631 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600631 / 500000) = 1/(500000 / 600631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18337267 / 100000000) (183372671 / 1000000000) (Real.log (600631 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (600631 / 500000) = -Real.log (500000 / 600631) := by
    rw [show ((600631 / 500000) : ℝ) = ((500000 / 600631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (28090287 / 125000000) ≤ -Real.log (399369 / 500000) ∧
    -Real.log (399369 / 500000) ≤ (224722297 / 1000000000) := by
  have h := checkLog_sound (w := (100631 / 899369)) (n := 12)
    (lo := (28090287 / 125000000)) (hi := (224722297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399369) = 1/(399369 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-224722297 / 1000000000) (-28090287 / 125000000) (Real.log (399369 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (183639021 / 1000000000) ≤ -Real.log (500000 / 600791) ∧
    -Real.log (500000 / 600791) ≤ (91819511 / 500000000) := by
  have h := checkLog_sound (w := (100791 / 1100791)) (n := 12)
    (lo := (183639021 / 1000000000)) (hi := (91819511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600791 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600791 / 500000) = 1/(500000 / 600791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (183639021 / 1000000000) (91819511 / 500000000) (Real.log (600791 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (600791 / 500000) = -Real.log (500000 / 600791) := by
    rw [show ((600791 / 500000) : ℝ) = ((500000 / 600791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (225123009 / 1000000000) ≤ -Real.log (399209 / 500000) ∧
    -Real.log (399209 / 500000) ≤ (22512301 / 100000000) := by
  have h := checkLog_sound (w := (100791 / 899209)) (n := 12)
    (lo := (225123009 / 1000000000)) (hi := (22512301 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399209) = 1/(399209 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-22512301 / 100000000) (-225123009 / 1000000000) (Real.log (399209 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (826457983 / 1000000000) ≤ -Real.log (31250000000 / 71412816811) ∧
    -Real.log (31250000000 / 71412816811) ≤ (165291597 / 200000000) := by
  have h := checkLog_sound (w := (8912816811 / 133912816811)) (n := 12)
    (lo := (133310803 / 1000000000)) (hi := (33327701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71412816811 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(71412816811 / 62500000000) = 1/(31250000000 / 71412816811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (826457983 / 1000000000) (165291597 / 200000000) (Real.log (71412816811 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (71412816811 / 31250000000) = -Real.log (31250000000 / 71412816811) := by
    rw [show ((71412816811 / 31250000000) : ℝ) = ((31250000000 / 71412816811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (827841993 / 1000000000) ≤ -Real.log (250000000000 / 572093770071) ∧
    -Real.log (250000000000 / 572093770071) ≤ (165568399 / 200000000) := by
  have h := checkLog_sound (w := (72093770071 / 1072093770071)) (n := 12)
    (lo := (134694813 / 1000000000)) (hi := (67347407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572093770071 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(572093770071 / 500000000000) = 1/(250000000000 / 572093770071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (827841993 / 1000000000) (165568399 / 200000000) (Real.log (572093770071 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (572093770071 / 250000000000) = -Real.log (250000000000 / 572093770071) := by
    rw [show ((572093770071 / 250000000000) : ℝ) = ((250000000000 / 572093770071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (286069301 / 500000000) ≤ -Real.log (500000000000 / 886026359449) ∧
    -Real.log (500000000000 / 886026359449) ≤ (572138603 / 1000000000) := by
  have h := checkLog_sound (w := (386026359449 / 1386026359449)) (n := 12)
    (lo := (286069301 / 500000000)) (hi := (572138603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((886026359449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(886026359449 / 500000000000) = 1/(500000000000 / 886026359449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (286069301 / 500000000) (572138603 / 1000000000) (Real.log (886026359449 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (886026359449 / 500000000000) = -Real.log (500000000000 / 886026359449) := by
    rw [show ((886026359449 / 500000000000) : ℝ) = ((500000000000 / 886026359449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (573060199 / 1000000000) ≤ -Real.log (500000000000 / 886843295029) ∧
    -Real.log (500000000000 / 886843295029) ≤ (2865301 / 5000000) := by
  have h := checkLog_sound (w := (386843295029 / 1386843295029)) (n := 12)
    (lo := (573060199 / 1000000000)) (hi := (2865301 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((886843295029 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(886843295029 / 500000000000) = 1/(500000000000 / 886843295029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (573060199 / 1000000000) (2865301 / 5000000) (Real.log (886843295029 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (886843295029 / 500000000000) = -Real.log (500000000000 / 886843295029) := by
    rw [show ((886843295029 / 500000000000) : ℝ) = ((500000000000 / 886843295029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (408094967 / 1000000000) ≤ -Real.log (500000000000 / 751974990547) ∧
    -Real.log (500000000000 / 751974990547) ≤ (51011871 / 125000000) := by
  have h := checkLog_sound (w := (251974990547 / 1251974990547)) (n := 12)
    (lo := (408094967 / 1000000000)) (hi := (51011871 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751974990547 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751974990547 / 500000000000) = 1/(500000000000 / 751974990547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (408094967 / 1000000000) (51011871 / 125000000) (Real.log (751974990547 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (751974990547 / 500000000000) = -Real.log (500000000000 / 751974990547) := by
    rw [show ((751974990547 / 500000000000) : ℝ) = ((500000000000 / 751974990547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (408762031 / 1000000000) ≤ -Real.log (500000000000 / 752476772819) ∧
    -Real.log (500000000000 / 752476772819) ≤ (25547627 / 62500000) := by
  have h := checkLog_sound (w := (252476772819 / 1252476772819)) (n := 12)
    (lo := (408762031 / 1000000000)) (hi := (25547627 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((752476772819 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(752476772819 / 500000000000) = 1/(500000000000 / 752476772819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (408762031 / 1000000000) (25547627 / 62500000) (Real.log (752476772819 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (752476772819 / 500000000000) = -Real.log (500000000000 / 752476772819) := by
    rw [show ((752476772819 / 500000000000) : ℝ) = ((500000000000 / 752476772819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (41483987 / 1000000000) ≤ -Real.log (239841174319 / 250000000000) ∧
    -Real.log (239841174319 / 250000000000) ≤ (10370997 / 250000000) := by
  have h := checkLog_sound (w := (10158825681 / 489841174319)) (n := 12)
    (lo := (41483987 / 1000000000)) (hi := (10370997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239841174319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239841174319) = 1/(239841174319 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-10370997 / 250000000) (-41483987 / 1000000000) (Real.log (239841174319 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20674813 / 500000000) ≤ -Real.log (239873401839 / 250000000000) ∧
    -Real.log (239873401839 / 250000000000) ≤ (41349627 / 1000000000) := by
  have h := checkLog_sound (w := (10126598161 / 489873401839)) (n := 12)
    (lo := (20674813 / 500000000)) (hi := (41349627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239873401839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239873401839) = 1/(239873401839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-41349627 / 1000000000) (-20674813 / 500000000) (Real.log (239873401839 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell241
