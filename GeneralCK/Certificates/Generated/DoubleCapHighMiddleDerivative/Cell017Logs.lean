import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell017
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

theorem reflection_log_1_neg : (115772827 / 500000000) ≤ -Real.log (2560 / 3227) ∧
    -Real.log (2560 / 3227) ≤ (46309131 / 200000000) := by
  have h := checkLog_sound (w := (667 / 5787)) (n := 12)
    (lo := (115772827 / 500000000)) (hi := (46309131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3227 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3227 / 2560) = 1/(2560 / 3227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (115772827 / 500000000) (46309131 / 200000000) (Real.log (3227 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3227 / 2560) = -Real.log (2560 / 3227) := by
    rw [show ((3227 / 2560) : ℝ) = ((2560 / 3227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (150922193 / 500000000) ≤ -Real.log (1893 / 2560) ∧
    -Real.log (1893 / 2560) ≤ (301844387 / 1000000000) := by
  have h := checkLog_sound (w := (667 / 4453)) (n := 12)
    (lo := (150922193 / 500000000)) (hi := (301844387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1893) = 1/(1893 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-301844387 / 1000000000) (-150922193 / 500000000) (Real.log (1893 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (115540359 / 500000000) ≤ -Real.log (5120 / 6451) ∧
    -Real.log (5120 / 6451) ≤ (231080719 / 1000000000) := by
  have h := checkLog_sound (w := (1331 / 11571)) (n := 12)
    (lo := (115540359 / 500000000)) (hi := (231080719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6451 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6451 / 5120) = 1/(5120 / 6451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (115540359 / 500000000) (231080719 / 1000000000) (Real.log (6451 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6451 / 5120) = -Real.log (5120 / 6451) := by
    rw [show ((6451 / 5120) : ℝ) = ((5120 / 6451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (301052307 / 1000000000) ≤ -Real.log (3789 / 5120) ∧
    -Real.log (3789 / 5120) ≤ (75263077 / 250000000) := by
  have h := checkLog_sound (w := (1331 / 8909)) (n := 12)
    (lo := (301052307 / 1000000000)) (hi := (75263077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3789) = 1/(3789 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-75263077 / 250000000) (-301052307 / 1000000000) (Real.log (3789 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (169195789 / 1000000000) ≤ -Real.log (31250 / 37011) ∧
    -Real.log (31250 / 37011) ≤ (16919579 / 100000000) := by
  have h := checkLog_sound (w := (5761 / 68261)) (n := 12)
    (lo := (169195789 / 1000000000)) (hi := (16919579 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37011 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37011 / 31250) = 1/(31250 / 37011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (169195789 / 1000000000) (16919579 / 100000000) (Real.log (37011 / 31250)) := by
  have h := reflection_log_5_neg
  have he : Real.log (37011 / 31250) = -Real.log (31250 / 37011) := by
    rw [show ((37011 / 31250) : ℝ) = ((31250 / 37011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (203772389 / 1000000000) ≤ -Real.log (25489 / 31250) ∧
    -Real.log (25489 / 31250) ≤ (20377239 / 100000000) := by
  have h := checkLog_sound (w := (5761 / 56739)) (n := 12)
    (lo := (203772389 / 1000000000)) (hi := (20377239 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 25489) = 1/(25489 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-20377239 / 100000000) (-203772389 / 1000000000) (Real.log (25489 / 31250)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (84774753 / 500000000) ≤ -Real.log (1000000 / 1184771) ∧
    -Real.log (1000000 / 1184771) ≤ (169549507 / 1000000000) := by
  have h := checkLog_sound (w := (184771 / 2184771)) (n := 12)
    (lo := (84774753 / 500000000)) (hi := (169549507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1184771 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1184771 / 1000000) = 1/(1000000 / 1184771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (84774753 / 500000000) (169549507 / 1000000000) (Real.log (1184771 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1184771 / 1000000) = -Real.log (1000000 / 1184771) := by
    rw [show ((1184771 / 1000000) : ℝ) = ((1000000 / 1184771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (204286223 / 1000000000) ≤ -Real.log (815229 / 1000000) ∧
    -Real.log (815229 / 1000000) ≤ (12767889 / 62500000) := by
  have h := checkLog_sound (w := (184771 / 1815229)) (n := 12)
    (lo := (204286223 / 1000000000)) (hi := (12767889 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 815229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 815229) = 1/(815229 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12767889 / 62500000) (-204286223 / 1000000000) (Real.log (815229 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4945161 / 40000000) ≤ -Real.log (250000 / 282899) ∧
    -Real.log (250000 / 282899) ≤ (61814513 / 500000000) := by
  have h := checkLog_sound (w := (32899 / 532899)) (n := 12)
    (lo := (4945161 / 40000000)) (hi := (61814513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((282899 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(282899 / 250000) = 1/(250000 / 282899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4945161 / 40000000) (61814513 / 500000000) (Real.log (282899 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (282899 / 250000) = -Real.log (250000 / 282899) := by
    rw [show ((282899 / 250000) : ℝ) = ((250000 / 282899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (70549117 / 500000000) ≤ -Real.log (217101 / 250000) ∧
    -Real.log (217101 / 250000) ≤ (28219647 / 200000000) := by
  have h := checkLog_sound (w := (32899 / 467101)) (n := 12)
    (lo := (70549117 / 500000000)) (hi := (28219647 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 217101) = 1/(217101 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-28219647 / 200000000) (-70549117 / 500000000) (Real.log (217101 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3097463 / 25000000) ≤ -Real.log (1000000 / 1131901) ∧
    -Real.log (1000000 / 1131901) ≤ (123898521 / 1000000000) := by
  have h := checkLog_sound (w := (131901 / 2131901)) (n := 12)
    (lo := (3097463 / 25000000)) (hi := (123898521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131901 / 1000000) = 1/(1000000 / 1131901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3097463 / 25000000) (123898521 / 1000000000) (Real.log (1131901 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1131901 / 1000000) = -Real.log (1000000 / 1131901) := by
    rw [show ((1131901 / 1000000) : ℝ) = ((1000000 / 1131901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (28289903 / 200000000) ≤ -Real.log (868099 / 1000000) ∧
    -Real.log (868099 / 1000000) ≤ (35362379 / 250000000) := by
  have h := checkLog_sound (w := (131901 / 1868099)) (n := 12)
    (lo := (28289903 / 200000000)) (hi := (35362379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 868099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 868099) = 1/(868099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-35362379 / 250000000) (-28289903 / 200000000) (Real.log (868099 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (21285321 / 40000000) ≤ -Real.log (500000000000 / 851280021113) ∧
    -Real.log (500000000000 / 851280021113) ≤ (266066513 / 500000000) := by
  have h := checkLog_sound (w := (351280021113 / 1351280021113)) (n := 12)
    (lo := (21285321 / 40000000)) (hi := (266066513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851280021113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851280021113 / 500000000000) = 1/(500000000000 / 851280021113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (21285321 / 40000000) (266066513 / 500000000) (Real.log (851280021113 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (851280021113 / 500000000000) = -Real.log (500000000000 / 851280021113) := by
    rw [show ((851280021113 / 500000000000) : ℝ) = ((500000000000 / 851280021113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (13334751 / 25000000) ≤ -Real.log (25000000000 / 42617538299) ∧
    -Real.log (25000000000 / 42617538299) ≤ (533390041 / 1000000000) := by
  have h := checkLog_sound (w := (17617538299 / 67617538299)) (n := 12)
    (lo := (13334751 / 25000000)) (hi := (533390041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42617538299 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42617538299 / 25000000000) = 1/(25000000000 / 42617538299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (13334751 / 25000000) (533390041 / 1000000000) (Real.log (42617538299 / 25000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (42617538299 / 25000000000) = -Real.log (25000000000 / 42617538299) := by
    rw [show ((42617538299 / 25000000000) : ℝ) = ((25000000000 / 42617538299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (372968179 / 1000000000) ≤ -Real.log (62500000000 / 90752383381) ∧
    -Real.log (62500000000 / 90752383381) ≤ (18648409 / 50000000) := by
  have h := checkLog_sound (w := (28252383381 / 153252383381)) (n := 12)
    (lo := (372968179 / 1000000000)) (hi := (18648409 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90752383381 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90752383381 / 62500000000) = 1/(62500000000 / 90752383381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (372968179 / 1000000000) (18648409 / 50000000) (Real.log (90752383381 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (90752383381 / 62500000000) = -Real.log (62500000000 / 90752383381) := by
    rw [show ((90752383381 / 62500000000) : ℝ) = ((62500000000 / 90752383381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (37383573 / 100000000) ≤ -Real.log (500000000000 / 726649199183) ∧
    -Real.log (500000000000 / 726649199183) ≤ (373835731 / 1000000000) := by
  have h := checkLog_sound (w := (226649199183 / 1226649199183)) (n := 12)
    (lo := (37383573 / 100000000)) (hi := (373835731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726649199183 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726649199183 / 500000000000) = 1/(500000000000 / 726649199183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (37383573 / 100000000) (373835731 / 1000000000) (Real.log (726649199183 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (726649199183 / 500000000000) = -Real.log (500000000000 / 726649199183) := by
    rw [show ((726649199183 / 500000000000) : ℝ) = ((500000000000 / 726649199183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (13236363 / 50000000) ≤ -Real.log (500000000000 / 651537763529) ∧
    -Real.log (500000000000 / 651537763529) ≤ (264727261 / 1000000000) := by
  have h := checkLog_sound (w := (151537763529 / 1151537763529)) (n := 12)
    (lo := (13236363 / 50000000)) (hi := (264727261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651537763529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651537763529 / 500000000000) = 1/(500000000000 / 651537763529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (13236363 / 50000000) (264727261 / 1000000000) (Real.log (651537763529 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (651537763529 / 500000000000) = -Real.log (500000000000 / 651537763529) := by
    rw [show ((651537763529 / 500000000000) : ℝ) = ((500000000000 / 651537763529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (53069607 / 200000000) ≤ -Real.log (50000000000 / 65194234759) ∧
    -Real.log (50000000000 / 65194234759) ≤ (66337009 / 250000000) := by
  have h := checkLog_sound (w := (15194234759 / 115194234759)) (n := 12)
    (lo := (53069607 / 200000000)) (hi := (66337009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65194234759 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65194234759 / 50000000000) = 1/(50000000000 / 65194234759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (53069607 / 200000000) (66337009 / 250000000) (Real.log (65194234759 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (65194234759 / 50000000000) = -Real.log (50000000000 / 65194234759) := by
    rw [show ((65194234759 / 50000000000) : ℝ) = ((50000000000 / 65194234759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3510199 / 200000000) ≤ -Real.log (982602126199 / 1000000000000) ∧
    -Real.log (982602126199 / 1000000000000) ≤ (4387749 / 250000000) := by
  have h := checkLog_sound (w := (17397873801 / 1982602126199)) (n := 12)
    (lo := (3510199 / 200000000)) (hi := (4387749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982602126199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982602126199) = 1/(982602126199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4387749 / 250000000) (-3510199 / 200000000) (Real.log (982602126199 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17469209 / 1000000000) ≤ -Real.log (61417655799 / 62500000000) ∧
    -Real.log (61417655799 / 62500000000) ≤ (1746921 / 100000000) := by
  have h := checkLog_sound (w := (1082344201 / 123917655799)) (n := 12)
    (lo := (17469209 / 1000000000)) (hi := (1746921 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61417655799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61417655799) = 1/(61417655799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1746921 / 100000000) (-17469209 / 1000000000) (Real.log (61417655799 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell017
