import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0279
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

theorem reflection_log_1_neg : (28691171 / 125000000) ≤ -Real.log (5120 / 6441) ∧
    -Real.log (5120 / 6441) ≤ (229529369 / 1000000000) := by
  have h := checkLog_sound (w := (1321 / 11561)) (n := 12)
    (lo := (28691171 / 125000000)) (hi := (229529369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6441 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6441 / 5120) = 1/(5120 / 6441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (28691171 / 125000000) (229529369 / 1000000000) (Real.log (6441 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6441 / 5120) = -Real.log (5120 / 6441) := by
    rw [show ((6441 / 5120) : ℝ) = ((5120 / 6441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (74604141 / 250000000) ≤ -Real.log (3799 / 5120) ∧
    -Real.log (3799 / 5120) ≤ (59683313 / 200000000) := by
  have h := checkLog_sound (w := (1321 / 8919)) (n := 12)
    (lo := (74604141 / 250000000)) (hi := (59683313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3799) = 1/(3799 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-59683313 / 200000000) (-74604141 / 250000000) (Real.log (3799 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (229063493 / 1000000000) ≤ -Real.log (2560 / 3219) ∧
    -Real.log (2560 / 3219) ≤ (114531747 / 500000000) := by
  have h := checkLog_sound (w := (659 / 5779)) (n := 12)
    (lo := (229063493 / 1000000000)) (hi := (114531747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3219 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3219 / 2560) = 1/(2560 / 3219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (229063493 / 1000000000) (114531747 / 500000000) (Real.log (3219 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3219 / 2560) = -Real.log (2560 / 3219) := by
    rw [show ((3219 / 2560) : ℝ) = ((2560 / 3219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (148813597 / 500000000) ≤ -Real.log (1901 / 2560) ∧
    -Real.log (1901 / 2560) ≤ (59525439 / 200000000) := by
  have h := checkLog_sound (w := (659 / 4461)) (n := 12)
    (lo := (148813597 / 500000000)) (hi := (59525439 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1901) = 1/(1901 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-59525439 / 200000000) (-148813597 / 500000000) (Real.log (1901 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (416085593 / 1000000000) ≤ -Real.log (2560 / 3881) ∧
    -Real.log (2560 / 3881) ≤ (208042797 / 500000000) := by
  have h := checkLog_sound (w := (1321 / 6441)) (n := 12)
    (lo := (416085593 / 1000000000)) (hi := (208042797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3881 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3881 / 2560) = 1/(2560 / 3881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (416085593 / 1000000000) (208042797 / 500000000) (Real.log (3881 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3881 / 2560) = -Real.log (2560 / 3881) := by
    rw [show ((3881 / 2560) : ℝ) = ((2560 / 3881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (145140531 / 200000000) ≤ -Real.log (1239 / 2560) ∧
    -Real.log (1239 / 2560) ≤ (725702657 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 2519)) (n := 12)
    (lo := (1302219 / 40000000)) (hi := (8138869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1239) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1239) = 1/(1239 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-725702657 / 1000000000) (-145140531 / 200000000) (Real.log (1239 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (207656149 / 500000000) ≤ -Real.log (1280 / 1939) ∧
    -Real.log (1280 / 1939) ≤ (415312299 / 1000000000) := by
  have h := checkLog_sound (w := (659 / 3219)) (n := 12)
    (lo := (207656149 / 500000000)) (hi := (415312299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1939 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1939 / 1280) = 1/(1280 / 1939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (207656149 / 500000000) (415312299 / 1000000000) (Real.log (1939 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1939 / 1280) = -Real.log (1280 / 1939) := by
    rw [show ((1939 / 1280) : ℝ) = ((1280 / 1939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (361642137 / 500000000) ≤ -Real.log (621 / 1280) ∧
    -Real.log (621 / 1280) ≤ (180821069 / 250000000) := by
  have h := checkLog_sound (w := (19 / 1261)) (n := 12)
    (lo := (15068547 / 500000000)) (hi := (6027419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 621) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 621) = 1/(621 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-180821069 / 250000000) (-361642137 / 500000000) (Real.log (621 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (15688941 / 50000000) ≤ -Real.log (1000000 / 1368587) ∧
    -Real.log (1000000 / 1368587) ≤ (313778821 / 1000000000) := by
  have h := checkLog_sound (w := (368587 / 2368587)) (n := 12)
    (lo := (15688941 / 50000000)) (hi := (313778821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1368587 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1368587 / 1000000) = 1/(1000000 / 1368587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (15688941 / 50000000) (313778821 / 1000000000) (Real.log (1368587 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1368587 / 1000000) = -Real.log (1000000 / 1368587) := by
    rw [show ((1368587 / 1000000) : ℝ) = ((1000000 / 1368587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (459795113 / 1000000000) ≤ -Real.log (631413 / 1000000) ∧
    -Real.log (631413 / 1000000) ≤ (229897557 / 500000000) := by
  have h := checkLog_sound (w := (368587 / 1631413)) (n := 12)
    (lo := (459795113 / 1000000000)) (hi := (229897557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 631413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 631413) = 1/(631413 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-229897557 / 500000000) (-459795113 / 1000000000) (Real.log (631413 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (314409929 / 1000000000) ≤ -Real.log (1000000 / 1369451) ∧
    -Real.log (1000000 / 1369451) ≤ (31440993 / 100000000) := by
  have h := checkLog_sound (w := (369451 / 2369451)) (n := 12)
    (lo := (314409929 / 1000000000)) (hi := (31440993 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1369451 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1369451 / 1000000) = 1/(1000000 / 1369451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (314409929 / 1000000000) (31440993 / 100000000) (Real.log (1369451 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1369451 / 1000000) = -Real.log (1000000 / 1369451) := by
    rw [show ((1369451 / 1000000) : ℝ) = ((1000000 / 1369451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (46116441 / 100000000) ≤ -Real.log (630549 / 1000000) ∧
    -Real.log (630549 / 1000000) ≤ (461164411 / 1000000000) := by
  have h := checkLog_sound (w := (369451 / 1630549)) (n := 12)
    (lo := (46116441 / 100000000)) (hi := (461164411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 630549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 630549) = 1/(630549 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-461164411 / 1000000000) (-46116441 / 100000000) (Real.log (630549 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (239652131 / 1000000000) ≤ -Real.log (1000000 / 1270807) ∧
    -Real.log (1000000 / 1270807) ≤ (59913033 / 250000000) := by
  have h := checkLog_sound (w := (270807 / 2270807)) (n := 12)
    (lo := (239652131 / 1000000000)) (hi := (59913033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1270807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1270807 / 1000000) = 1/(1000000 / 1270807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (239652131 / 1000000000) (59913033 / 250000000) (Real.log (1270807 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1270807 / 1000000) = -Real.log (1000000 / 1270807) := by
    rw [show ((1270807 / 1000000) : ℝ) = ((1000000 / 1270807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (63163367 / 200000000) ≤ -Real.log (729193 / 1000000) ∧
    -Real.log (729193 / 1000000) ≤ (78954209 / 250000000) := by
  have h := checkLog_sound (w := (270807 / 1729193)) (n := 12)
    (lo := (63163367 / 200000000)) (hi := (78954209 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 729193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 729193) = 1/(729193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-78954209 / 250000000) (-63163367 / 200000000) (Real.log (729193 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (240190227 / 1000000000) ≤ -Real.log (1000000 / 1271491) ∧
    -Real.log (1000000 / 1271491) ≤ (60047557 / 250000000) := by
  have h := checkLog_sound (w := (271491 / 2271491)) (n := 12)
    (lo := (240190227 / 1000000000)) (hi := (60047557 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1271491 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1271491 / 1000000) = 1/(1000000 / 1271491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (240190227 / 1000000000) (60047557 / 250000000) (Real.log (1271491 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1271491 / 1000000) = -Real.log (1000000 / 1271491) := by
    rw [show ((1271491 / 1000000) : ℝ) = ((1000000 / 1271491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (316755299 / 1000000000) ≤ -Real.log (728509 / 1000000) ∧
    -Real.log (728509 / 1000000) ≤ (3167553 / 10000000) := by
  have h := checkLog_sound (w := (271491 / 1728509)) (n := 12)
    (lo := (316755299 / 1000000000)) (hi := (3167553 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 728509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 728509) = 1/(728509 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3167553 / 10000000) (-316755299 / 1000000000) (Real.log (728509 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (386786967 / 500000000) ≤ -Real.log (31250000000 / 67734341469) ∧
    -Real.log (31250000000 / 67734341469) ≤ (48348371 / 62500000) := by
  have h := checkLog_sound (w := (5234341469 / 130234341469)) (n := 12)
    (lo := (40213377 / 500000000)) (hi := (16085351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67734341469 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(67734341469 / 62500000000) = 1/(31250000000 / 67734341469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (386786967 / 500000000) (48348371 / 62500000) (Real.log (67734341469 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (67734341469 / 31250000000) = -Real.log (31250000000 / 67734341469) := by
    rw [show ((67734341469 / 31250000000) : ℝ) = ((31250000000 / 67734341469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (775574339 / 1000000000) ≤ -Real.log (20000000000 / 43436782867) ∧
    -Real.log (20000000000 / 43436782867) ≤ (775574341 / 1000000000) := by
  have h := checkLog_sound (w := (3436782867 / 83436782867)) (n := 12)
    (lo := (82427159 / 1000000000)) (hi := (2060679 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43436782867 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(43436782867 / 40000000000) = 1/(20000000000 / 43436782867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (775574339 / 1000000000) (775574341 / 1000000000) (Real.log (43436782867 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (43436782867 / 20000000000) = -Real.log (20000000000 / 43436782867) := by
    rw [show ((43436782867 / 20000000000) : ℝ) = ((20000000000 / 43436782867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (555468967 / 1000000000) ≤ -Real.log (500000000000 / 871379045053) ∧
    -Real.log (500000000000 / 871379045053) ≤ (69433621 / 125000000) := by
  have h := checkLog_sound (w := (371379045053 / 1371379045053)) (n := 12)
    (lo := (555468967 / 1000000000)) (hi := (69433621 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871379045053 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(871379045053 / 500000000000) = 1/(500000000000 / 871379045053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (555468967 / 1000000000) (69433621 / 125000000) (Real.log (871379045053 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (871379045053 / 500000000000) = -Real.log (500000000000 / 871379045053) := by
    rw [show ((871379045053 / 500000000000) : ℝ) = ((500000000000 / 871379045053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (278472763 / 500000000) ≤ -Real.log (500000000000 / 872666638299) ∧
    -Real.log (500000000000 / 872666638299) ≤ (556945527 / 1000000000) := by
  have h := checkLog_sound (w := (372666638299 / 1372666638299)) (n := 12)
    (lo := (278472763 / 500000000)) (hi := (556945527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((872666638299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(872666638299 / 500000000000) = 1/(500000000000 / 872666638299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (278472763 / 500000000) (556945527 / 1000000000) (Real.log (872666638299 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (872666638299 / 500000000000) = -Real.log (500000000000 / 872666638299) := by
    rw [show ((872666638299 / 500000000000) : ℝ) = ((500000000000 / 872666638299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0279
