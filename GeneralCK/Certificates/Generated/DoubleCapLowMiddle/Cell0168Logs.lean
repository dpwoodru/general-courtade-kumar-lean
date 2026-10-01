import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0168
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

theorem reflection_log_1_neg : (639424951 / 1000000000) ≤ -Real.log (12800 / 24261) ∧
    -Real.log (12800 / 24261) ≤ (79928119 / 125000000) := by
  have h := checkLog_sound (w := (11461 / 37061)) (n := 12)
    (lo := (639424951 / 1000000000)) (hi := (79928119 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24261 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24261 / 12800) = 1/(12800 / 24261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (639424951 / 1000000000) (79928119 / 125000000) (Real.log (24261 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24261 / 12800) = -Real.log (12800 / 24261) := by
    rw [show ((24261 / 12800) : ℝ) = ((12800 / 24261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1128761051 / 500000000) ≤ -Real.log (1339 / 12800) ∧
    -Real.log (1339 / 12800) ≤ (1128761053 / 500000000) := by
  have h := checkLog_sound (w := (261 / 2939)) (n := 12)
    (lo := (89040281 / 500000000)) (hi := (178080563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1339) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1339) = 1/(1339 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1128761053 / 500000000) (-1128761051 / 500000000) (Real.log (1339 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (127728299 / 200000000) ≤ -Real.log (6400 / 12121) ∧
    -Real.log (6400 / 12121) ≤ (79830187 / 125000000) := by
  have h := checkLog_sound (w := (5721 / 18521)) (n := 12)
    (lo := (127728299 / 200000000)) (hi := (79830187 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12121 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12121 / 6400) = 1/(6400 / 12121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (127728299 / 200000000) (79830187 / 125000000) (Real.log (12121 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12121 / 6400) = -Real.log (6400 / 12121) := by
    rw [show ((12121 / 6400) : ℝ) = ((6400 / 12121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (112171607 / 50000000) ≤ -Real.log (679 / 6400) ∧
    -Real.log (679 / 6400) ≤ (140214509 / 62500000) := by
  have h := checkLog_sound (w := (121 / 1479)) (n := 12)
    (lo := (819953 / 5000000)) (hi := (163990601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 679) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 679) = 1/(679 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-140214509 / 62500000) (-112171607 / 50000000) (Real.log (679 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (582651977 / 1000000000) ≤ -Real.log (6400 / 11461) ∧
    -Real.log (6400 / 11461) ≤ (291325989 / 500000000) := by
  have h := checkLog_sound (w := (5061 / 17861)) (n := 12)
    (lo := (582651977 / 1000000000)) (hi := (291325989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11461 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11461 / 6400) = 1/(6400 / 11461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (582651977 / 1000000000) (291325989 / 500000000) (Real.log (11461 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11461 / 6400) = -Real.log (6400 / 11461) := by
    rw [show ((11461 / 6400) : ℝ) = ((6400 / 11461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (782187461 / 500000000) ≤ -Real.log (1339 / 6400) ∧
    -Real.log (1339 / 6400) ≤ (62574997 / 40000000) := by
  have h := checkLog_sound (w := (261 / 2939)) (n := 12)
    (lo := (89040281 / 500000000)) (hi := (178080563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1339) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1339) = 1/(1339 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-62574997 / 40000000) (-782187461 / 500000000) (Real.log (1339 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (116198561 / 200000000) ≤ -Real.log (3200 / 5721) ∧
    -Real.log (3200 / 5721) ≤ (290496403 / 500000000) := by
  have h := checkLog_sound (w := (2521 / 8921)) (n := 12)
    (lo := (116198561 / 200000000)) (hi := (290496403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5721 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5721 / 3200) = 1/(3200 / 5721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (116198561 / 200000000) (290496403 / 500000000) (Real.log (5721 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5721 / 3200) = -Real.log (3200 / 5721) := by
    rw [show ((5721 / 3200) : ℝ) = ((3200 / 5721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (9689281 / 6250000) ≤ -Real.log (679 / 3200) ∧
    -Real.log (679 / 3200) ≤ (1550284963 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 1479)) (n := 12)
    (lo := (819953 / 5000000)) (hi := (163990601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 679) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 679) = 1/(679 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1550284963 / 1000000000) (-9689281 / 6250000) (Real.log (679 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (651933963 / 1000000000) ≤ -Real.log (1000000 / 1919249) ∧
    -Real.log (1000000 / 1919249) ≤ (162983491 / 250000000) := by
  have h := checkLog_sound (w := (919249 / 2919249)) (n := 12)
    (lo := (651933963 / 1000000000)) (hi := (162983491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1919249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1919249 / 1000000) = 1/(1000000 / 1919249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (651933963 / 1000000000) (162983491 / 250000000) (Real.log (1919249 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1919249 / 1000000) = -Real.log (1000000 / 1919249) := by
    rw [show ((1919249 / 1000000) : ℝ) = ((1000000 / 1919249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2516384931 / 1000000000) ≤ -Real.log (80751 / 1000000) ∧
    -Real.log (80751 / 1000000) ≤ (503276987 / 200000000) := by
  have h := checkLog_sound (w := (44249 / 205751)) (n := 12)
    (lo := (436943391 / 1000000000)) (hi := (13654481 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80751) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 80751) = 1/(80751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-503276987 / 200000000) (-2516384931 / 1000000000) (Real.log (80751 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (130491077 / 200000000) ≤ -Real.log (4000 / 7681) ∧
    -Real.log (4000 / 7681) ≤ (326227693 / 500000000) := by
  have h := checkLog_sound (w := (3681 / 11681)) (n := 12)
    (lo := (130491077 / 200000000)) (hi := (326227693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7681 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7681 / 4000) = 1/(4000 / 7681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (130491077 / 200000000) (326227693 / 500000000) (Real.log (7681 / 4000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (7681 / 4000) = -Real.log (4000 / 7681) := by
    rw [show ((7681 / 4000) : ℝ) = ((4000 / 7681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (505771707 / 200000000) ≤ -Real.log (319 / 4000) ∧
    -Real.log (319 / 4000) ≤ (2528858539 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 819)) (n := 12)
    (lo := (89883399 / 200000000)) (hi := (112354249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 319) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(500 / 319) = 1/(319 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2528858539 / 1000000000) (-505771707 / 200000000) (Real.log (319 / 4000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (325258651 / 500000000) ≤ -Real.log (250000 / 479133) ∧
    -Real.log (250000 / 479133) ≤ (650517303 / 1000000000) := by
  have h := checkLog_sound (w := (229133 / 729133)) (n := 12)
    (lo := (325258651 / 500000000)) (hi := (650517303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479133 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479133 / 250000) = 1/(250000 / 479133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (325258651 / 500000000) (650517303 / 1000000000) (Real.log (479133 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (479133 / 250000) = -Real.log (250000 / 479133) := by
    rw [show ((479133 / 250000) : ℝ) = ((250000 / 479133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (155205747 / 62500000) ≤ -Real.log (20867 / 250000) ∧
    -Real.log (20867 / 250000) ≤ (620822989 / 250000000) := by
  have h := checkLog_sound (w := (10383 / 52117)) (n := 12)
    (lo := (100962603 / 250000000)) (hi := (403850413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20867) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 20867) = 1/(20867 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-620822989 / 250000000) (-155205747 / 62500000) (Real.log (20867 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (130217071 / 200000000) ≤ -Real.log (1000000 / 1917621) ∧
    -Real.log (1000000 / 1917621) ≤ (162771339 / 250000000) := by
  have h := checkLog_sound (w := (917621 / 2917621)) (n := 12)
    (lo := (130217071 / 200000000)) (hi := (162771339 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1917621 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1917621 / 1000000) = 1/(1000000 / 1917621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (130217071 / 200000000) (162771339 / 250000000) (Real.log (1917621 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1917621 / 1000000) = -Real.log (1000000 / 1917621) := by
    rw [show ((1917621 / 1000000) : ℝ) = ((1000000 / 1917621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2496424727 / 1000000000) ≤ -Real.log (82379 / 1000000) ∧
    -Real.log (82379 / 1000000) ≤ (2496424731 / 1000000000) := by
  have h := checkLog_sound (w := (42621 / 207379)) (n := 12)
    (lo := (416983187 / 1000000000)) (hi := (104245797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 82379) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 82379) = 1/(82379 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2496424731 / 1000000000) (-2496424727 / 1000000000) (Real.log (82379 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1584159447 / 500000000) ≤ -Real.log (500000000000 / 11883747569689) ∧
    -Real.log (500000000000 / 11883747569689) ≤ (3168318899 / 1000000000) := by
  have h := checkLog_sound (w := (3883747569689 / 19883747569689)) (n := 12)
    (lo := (197865087 / 500000000)) (hi := (15829207 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11883747569689 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11883747569689 / 8000000000000) = 1/(500000000000 / 11883747569689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1584159447 / 500000000) (3168318899 / 1000000000) (Real.log (11883747569689 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11883747569689 / 500000000000) = -Real.log (500000000000 / 11883747569689) := by
    rw [show ((11883747569689 / 500000000000) : ℝ) = ((500000000000 / 11883747569689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4970803 / 1562500) ≤ -Real.log (500000000000 / 12039184952979) ∧
    -Real.log (500000000000 / 12039184952979) ≤ (127252557 / 40000000) := by
  have h := checkLog_sound (w := (4039184952979 / 20039184952979)) (n := 12)
    (lo := (1021813 / 2500000)) (hi := (408725201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12039184952979 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12039184952979 / 8000000000000) = 1/(500000000000 / 12039184952979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4970803 / 1562500) (127252557 / 40000000) (Real.log (12039184952979 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12039184952979 / 500000000000) = -Real.log (500000000000 / 12039184952979) := by
    rw [show ((12039184952979 / 500000000000) : ℝ) = ((500000000000 / 12039184952979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1566904627 / 500000000) ≤ -Real.log (3906250000 / 89692494429) ∧
    -Real.log (3906250000 / 89692494429) ≤ (3133809259 / 1000000000) := by
  have h := checkLog_sound (w := (27192494429 / 152192494429)) (n := 12)
    (lo := (180610267 / 500000000)) (hi := (72244107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89692494429 / 62500000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(89692494429 / 62500000000) = 1/(3906250000 / 89692494429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1566904627 / 500000000) (3133809259 / 1000000000) (Real.log (89692494429 / 3906250000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (89692494429 / 3906250000) = -Real.log (3906250000 / 89692494429) := by
    rw [show ((89692494429 / 3906250000) : ℝ) = ((3906250000 / 89692494429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3147510081 / 1000000000) ≤ -Real.log (500000000000 / 11639016011363) ∧
    -Real.log (500000000000 / 11639016011363) ≤ (1573755043 / 500000000) := by
  have h := checkLog_sound (w := (3639016011363 / 19639016011363)) (n := 12)
    (lo := (374921361 / 1000000000)) (hi := (187460681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11639016011363 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11639016011363 / 8000000000000) = 1/(500000000000 / 11639016011363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3147510081 / 1000000000) (1573755043 / 500000000) (Real.log (11639016011363 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (11639016011363 / 500000000000) = -Real.log (500000000000 / 11639016011363) := by
    rw [show ((11639016011363 / 500000000000) : ℝ) = ((500000000000 / 11639016011363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0168
