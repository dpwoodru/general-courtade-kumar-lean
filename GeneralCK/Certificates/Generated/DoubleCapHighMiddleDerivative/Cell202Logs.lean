import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell202
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

theorem reflection_log_1_neg : (157020299 / 500000000) ≤ -Real.log (5120 / 7009) ∧
    -Real.log (5120 / 7009) ≤ (314040599 / 1000000000) := by
  have h := checkLog_sound (w := (1889 / 12129)) (n := 12)
    (lo := (157020299 / 500000000)) (hi := (314040599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7009 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7009 / 5120) = 1/(5120 / 7009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (157020299 / 500000000) (314040599 / 1000000000) (Real.log (7009 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7009 / 5120) = -Real.log (5120 / 7009) := by
    rw [show ((7009 / 5120) : ℝ) = ((5120 / 7009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (899146 / 1953125) ≤ -Real.log (3231 / 5120) ∧
    -Real.log (3231 / 5120) ≤ (460362753 / 1000000000) := by
  have h := checkLog_sound (w := (1889 / 8351)) (n := 12)
    (lo := (899146 / 1953125)) (hi := (460362753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3231) = 1/(3231 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-460362753 / 1000000000) (-899146 / 1953125) (Real.log (3231 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (62722497 / 200000000) ≤ -Real.log (2560 / 3503) ∧
    -Real.log (2560 / 3503) ≤ (156806243 / 500000000) := by
  have h := checkLog_sound (w := (943 / 6063)) (n := 12)
    (lo := (62722497 / 200000000)) (hi := (156806243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3503 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3503 / 2560) = 1/(2560 / 3503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (62722497 / 200000000) (156806243 / 500000000) (Real.log (3503 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3503 / 2560) = -Real.log (2560 / 3503) := by
    rw [show ((3503 / 2560) : ℝ) = ((2560 / 3503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (459434677 / 1000000000) ≤ -Real.log (1617 / 2560) ∧
    -Real.log (1617 / 2560) ≤ (229717339 / 500000000) := by
  have h := checkLog_sound (w := (943 / 4177)) (n := 12)
    (lo := (459434677 / 1000000000)) (hi := (229717339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1617) = 1/(1617 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-229717339 / 500000000) (-459434677 / 1000000000) (Real.log (1617 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (29090291 / 125000000) ≤ -Real.log (1000000 / 1262031) ∧
    -Real.log (1000000 / 1262031) ≤ (232722329 / 1000000000) := by
  have h := checkLog_sound (w := (262031 / 2262031)) (n := 12)
    (lo := (29090291 / 125000000)) (hi := (232722329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1262031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1262031 / 1000000) = 1/(1000000 / 1262031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (29090291 / 125000000) (232722329 / 1000000000) (Real.log (1262031 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1262031 / 1000000) = -Real.log (1000000 / 1262031) := by
    rw [show ((1262031 / 1000000) : ℝ) = ((1000000 / 1262031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (15192673 / 50000000) ≤ -Real.log (737969 / 1000000) ∧
    -Real.log (737969 / 1000000) ≤ (303853461 / 1000000000) := by
  have h := checkLog_sound (w := (262031 / 1737969)) (n := 12)
    (lo := (15192673 / 50000000)) (hi := (303853461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 737969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 737969) = 1/(737969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-303853461 / 1000000000) (-15192673 / 50000000) (Real.log (737969 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (46611489 / 200000000) ≤ -Real.log (500000 / 631227) ∧
    -Real.log (500000 / 631227) ≤ (116528723 / 500000000) := by
  have h := checkLog_sound (w := (131227 / 1131227)) (n := 12)
    (lo := (46611489 / 200000000)) (hi := (116528723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((631227 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(631227 / 500000) = 1/(500000 / 631227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (46611489 / 200000000) (116528723 / 500000000) (Real.log (631227 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (631227 / 500000) = -Real.log (500000 / 631227) := by
    rw [show ((631227 / 500000) : ℝ) = ((500000 / 631227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (304426819 / 1000000000) ≤ -Real.log (368773 / 500000) ∧
    -Real.log (368773 / 500000) ≤ (15221341 / 50000000) := by
  have h := checkLog_sound (w := (131227 / 868773)) (n := 12)
    (lo := (304426819 / 1000000000)) (hi := (15221341 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 368773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 368773) = 1/(368773 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-15221341 / 50000000) (-304426819 / 1000000000) (Real.log (368773 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (86504161 / 500000000) ≤ -Real.log (250000 / 297219) ∧
    -Real.log (250000 / 297219) ≤ (173008323 / 1000000000) := by
  have h := checkLog_sound (w := (47219 / 547219)) (n := 12)
    (lo := (86504161 / 500000000)) (hi := (173008323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297219 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297219 / 250000) = 1/(250000 / 297219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (86504161 / 500000000) (173008323 / 1000000000) (Real.log (297219 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (297219 / 250000) = -Real.log (250000 / 297219) := by
    rw [show ((297219 / 250000) : ℝ) = ((250000 / 297219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (104667169 / 500000000) ≤ -Real.log (202781 / 250000) ∧
    -Real.log (202781 / 250000) ≤ (209334339 / 1000000000) := by
  have h := checkLog_sound (w := (47219 / 452781)) (n := 12)
    (lo := (104667169 / 500000000)) (hi := (209334339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 202781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 202781) = 1/(202781 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-209334339 / 1000000000) (-104667169 / 500000000) (Real.log (202781 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (6930997 / 40000000) ≤ -Real.log (1000000 / 1189193) ∧
    -Real.log (1000000 / 1189193) ≤ (86637463 / 500000000) := by
  have h := checkLog_sound (w := (189193 / 2189193)) (n := 12)
    (lo := (6930997 / 40000000)) (hi := (86637463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1189193 / 1000000) = 1/(1000000 / 1189193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (6930997 / 40000000) (86637463 / 500000000) (Real.log (1189193 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1189193 / 1000000) = -Real.log (1000000 / 1189193) := by
    rw [show ((1189193 / 1000000) : ℝ) = ((1000000 / 1189193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (20972523 / 100000000) ≤ -Real.log (810807 / 1000000) ∧
    -Real.log (810807 / 1000000) ≤ (209725231 / 1000000000) := by
  have h := checkLog_sound (w := (189193 / 1810807)) (n := 12)
    (lo := (20972523 / 100000000)) (hi := (209725231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 810807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 810807) = 1/(810807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-209725231 / 1000000000) (-20972523 / 100000000) (Real.log (810807 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (773047163 / 1000000000) ≤ -Real.log (100000000000 / 216635745207) ∧
    -Real.log (100000000000 / 216635745207) ≤ (154609433 / 200000000) := by
  have h := checkLog_sound (w := (16635745207 / 416635745207)) (n := 12)
    (lo := (79899983 / 1000000000)) (hi := (4993749 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216635745207 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(216635745207 / 200000000000) = 1/(100000000000 / 216635745207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (773047163 / 1000000000) (154609433 / 200000000) (Real.log (216635745207 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (216635745207 / 100000000000) = -Real.log (100000000000 / 216635745207) := by
    rw [show ((216635745207 / 100000000000) : ℝ) = ((100000000000 / 216635745207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (15488067 / 20000000) ≤ -Real.log (31250000000 / 67790544723) ∧
    -Real.log (31250000000 / 67790544723) ≤ (96800419 / 125000000) := by
  have h := checkLog_sound (w := (5290544723 / 130290544723)) (n := 12)
    (lo := (8125617 / 100000000)) (hi := (81256171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67790544723 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(67790544723 / 62500000000) = 1/(31250000000 / 67790544723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (15488067 / 20000000) (96800419 / 125000000) (Real.log (67790544723 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (67790544723 / 31250000000) = -Real.log (31250000000 / 67790544723) := by
    rw [show ((67790544723 / 31250000000) : ℝ) = ((31250000000 / 67790544723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (134143947 / 250000000) ≤ -Real.log (500000000000 / 855070470439) ∧
    -Real.log (500000000000 / 855070470439) ≤ (536575789 / 1000000000) := by
  have h := checkLog_sound (w := (355070470439 / 1355070470439)) (n := 12)
    (lo := (134143947 / 250000000)) (hi := (536575789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((855070470439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(855070470439 / 500000000000) = 1/(500000000000 / 855070470439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (134143947 / 250000000) (536575789 / 1000000000) (Real.log (855070470439 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (855070470439 / 500000000000) = -Real.log (500000000000 / 855070470439) := by
    rw [show ((855070470439 / 500000000000) : ℝ) = ((500000000000 / 855070470439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (107496853 / 200000000) ≤ -Real.log (500000000000 / 855847635267) ∧
    -Real.log (500000000000 / 855847635267) ≤ (268742133 / 500000000) := by
  have h := checkLog_sound (w := (355847635267 / 1355847635267)) (n := 12)
    (lo := (107496853 / 200000000)) (hi := (268742133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((855847635267 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(855847635267 / 500000000000) = 1/(500000000000 / 855847635267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (107496853 / 200000000) (268742133 / 500000000) (Real.log (855847635267 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (855847635267 / 500000000000) = -Real.log (500000000000 / 855847635267) := by
    rw [show ((855847635267 / 500000000000) : ℝ) = ((500000000000 / 855847635267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (382342661 / 1000000000) ≤ -Real.log (250000000000 / 366428560861) ∧
    -Real.log (250000000000 / 366428560861) ≤ (191171331 / 500000000) := by
  have h := checkLog_sound (w := (116428560861 / 616428560861)) (n := 12)
    (lo := (382342661 / 1000000000)) (hi := (191171331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366428560861 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366428560861 / 250000000000) = 1/(250000000000 / 366428560861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (382342661 / 1000000000) (191171331 / 500000000) (Real.log (366428560861 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (366428560861 / 250000000000) = -Real.log (250000000000 / 366428560861) := by
    rw [show ((366428560861 / 250000000000) : ℝ) = ((250000000000 / 366428560861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (95750039 / 250000000) ≤ -Real.log (125000000000 / 183334782507) ∧
    -Real.log (125000000000 / 183334782507) ≤ (383000157 / 1000000000) := by
  have h := checkLog_sound (w := (58334782507 / 308334782507)) (n := 12)
    (lo := (95750039 / 250000000)) (hi := (383000157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183334782507 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183334782507 / 125000000000) = 1/(125000000000 / 183334782507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (95750039 / 250000000) (383000157 / 1000000000) (Real.log (183334782507 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (183334782507 / 125000000000) = -Real.log (125000000000 / 183334782507) := by
    rw [show ((183334782507 / 125000000000) : ℝ) = ((125000000000 / 183334782507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7290061 / 200000000) ≤ -Real.log (964206008751 / 1000000000000) ∧
    -Real.log (964206008751 / 1000000000000) ≤ (18225153 / 500000000) := by
  have h := checkLog_sound (w := (35793991249 / 1964206008751)) (n := 12)
    (lo := (7290061 / 200000000)) (hi := (18225153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964206008751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964206008751) = 1/(964206008751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18225153 / 500000000) (-7290061 / 200000000) (Real.log (964206008751 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (7265203 / 200000000) ≤ -Real.log (60270366039 / 62500000000) ∧
    -Real.log (60270366039 / 62500000000) ≤ (283797 / 7812500) := by
  have h := checkLog_sound (w := (2229633961 / 122770366039)) (n := 12)
    (lo := (7265203 / 200000000)) (hi := (283797 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60270366039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60270366039) = 1/(60270366039 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-283797 / 7812500) (-7265203 / 200000000) (Real.log (60270366039 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell202
