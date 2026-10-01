import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0194
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

theorem reflection_log_1_neg : (150886807 / 250000000) ≤ -Real.log (6400 / 11703) ∧
    -Real.log (6400 / 11703) ≤ (603547229 / 1000000000) := by
  have h := checkLog_sound (w := (5303 / 18103)) (n := 12)
    (lo := (150886807 / 250000000)) (hi := (603547229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11703 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11703 / 6400) = 1/(6400 / 11703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (150886807 / 250000000) (603547229 / 1000000000) (Real.log (11703 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11703 / 6400) = -Real.log (6400 / 11703) := by
    rw [show ((11703 / 6400) : ℝ) = ((6400 / 11703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1763718807 / 1000000000) ≤ -Real.log (1097 / 6400) ∧
    -Real.log (1097 / 6400) ≤ (176371881 / 100000000) := by
  have h := checkLog_sound (w := (503 / 2697)) (n := 12)
    (lo := (377424447 / 1000000000)) (hi := (5897257 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1097) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1097) = 1/(1097 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-176371881 / 100000000) (-1763718807 / 1000000000) (Real.log (1097 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (300961197 / 500000000) ≤ -Real.log (1600 / 2921) ∧
    -Real.log (1600 / 2921) ≤ (120384479 / 200000000) := by
  have h := checkLog_sound (w := (1321 / 4521)) (n := 12)
    (lo := (300961197 / 500000000)) (hi := (120384479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2921 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2921 / 1600) = 1/(1600 / 2921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (300961197 / 500000000) (120384479 / 200000000) (Real.log (2921 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2921 / 1600) = -Real.log (1600 / 2921) := by
    rw [show ((2921 / 1600) : ℝ) = ((1600 / 2921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (13972377 / 8000000) ≤ -Real.log (279 / 1600) ∧
    -Real.log (279 / 1600) ≤ (218318391 / 125000000) := by
  have h := checkLog_sound (w := (121 / 679)) (n := 12)
    (lo := (72050553 / 200000000)) (hi := (180126383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 279) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 279) = 1/(279 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-218318391 / 125000000) (-13972377 / 8000000) (Real.log (279 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (15785059 / 31250000) ≤ -Real.log (3200 / 5303) ∧
    -Real.log (3200 / 5303) ≤ (505121889 / 1000000000) := by
  have h := checkLog_sound (w := (2103 / 8503)) (n := 12)
    (lo := (15785059 / 31250000)) (hi := (505121889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5303 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5303 / 3200) = 1/(3200 / 5303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (15785059 / 31250000) (505121889 / 1000000000) (Real.log (5303 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5303 / 3200) = -Real.log (3200 / 5303) := by
    rw [show ((5303 / 3200) : ℝ) = ((3200 / 5303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1070571627 / 1000000000) ≤ -Real.log (1097 / 3200) ∧
    -Real.log (1097 / 3200) ≤ (1070571629 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 2697)) (n := 12)
    (lo := (377424447 / 1000000000)) (hi := (5897257 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1097) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1097) = 1/(1097 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1070571629 / 1000000000) (-1070571627 / 1000000000) (Real.log (1097 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (15672893 / 31250000) ≤ -Real.log (800 / 1321) ∧
    -Real.log (800 / 1321) ≤ (501532577 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 2121)) (n := 12)
    (lo := (15672893 / 31250000)) (hi := (501532577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1321 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1321 / 800) = 1/(800 / 1321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (15672893 / 31250000) (501532577 / 1000000000) (Real.log (1321 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1321 / 800) = -Real.log (800 / 1321) := by
    rw [show ((1321 / 800) : ℝ) = ((800 / 1321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (210679989 / 200000000) ≤ -Real.log (279 / 800) ∧
    -Real.log (279 / 800) ≤ (1053399947 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 679)) (n := 12)
    (lo := (72050553 / 200000000)) (hi := (180126383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 279) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 279) = 1/(279 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1053399947 / 1000000000) (-210679989 / 200000000) (Real.log (279 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (629555943 / 1000000000) ≤ -Real.log (1000000 / 1876777) ∧
    -Real.log (1000000 / 1876777) ≤ (78694493 / 125000000) := by
  have h := checkLog_sound (w := (876777 / 2876777)) (n := 12)
    (lo := (629555943 / 1000000000)) (hi := (78694493 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1876777 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1876777 / 1000000) = 1/(1000000 / 1876777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (629555943 / 1000000000) (78694493 / 125000000) (Real.log (1876777 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1876777 / 1000000) = -Real.log (1000000 / 1876777) := by
    rw [show ((1876777 / 1000000) : ℝ) = ((1000000 / 1876777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (418751911 / 200000000) ≤ -Real.log (123223 / 1000000) ∧
    -Real.log (123223 / 1000000) ≤ (2093759559 / 1000000000) := by
  have h := checkLog_sound (w := (1777 / 248223)) (n := 12)
    (lo := (2863603 / 200000000)) (hi := (223719 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 123223) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 123223) = 1/(123223 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2093759559 / 1000000000) (-418751911 / 200000000) (Real.log (123223 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (630462939 / 1000000000) ≤ -Real.log (12500 / 23481) ∧
    -Real.log (12500 / 23481) ≤ (31523147 / 50000000) := by
  have h := checkLog_sound (w := (10981 / 35981)) (n := 12)
    (lo := (630462939 / 1000000000)) (hi := (31523147 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23481 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23481 / 12500) = 1/(12500 / 23481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (630462939 / 1000000000) (31523147 / 50000000) (Real.log (23481 / 12500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (23481 / 12500) = -Real.log (12500 / 23481) := by
    rw [show ((23481 / 12500) : ℝ) = ((12500 / 23481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2107676419 / 1000000000) ≤ -Real.log (1519 / 12500) ∧
    -Real.log (1519 / 12500) ≤ (2107676423 / 1000000000) := by
  have h := checkLog_sound (w := (87 / 6163)) (n := 12)
    (lo := (28234879 / 1000000000)) (hi := (44117 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3038) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3125 / 3038) = 1/(1519 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2107676423 / 1000000000) (-2107676419 / 1000000000) (Real.log (1519 / 12500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (624839431 / 1000000000) ≤ -Real.log (500000 / 933973) ∧
    -Real.log (500000 / 933973) ≤ (78104929 / 125000000) := by
  have h := checkLog_sound (w := (433973 / 1433973)) (n := 12)
    (lo := (624839431 / 1000000000)) (hi := (78104929 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((933973 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(933973 / 500000) = 1/(500000 / 933973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (624839431 / 1000000000) (78104929 / 125000000) (Real.log (933973 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (933973 / 500000) = -Real.log (500000 / 933973) := by
    rw [show ((933973 / 500000) : ℝ) = ((500000 / 933973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (506136087 / 250000000) ≤ -Real.log (66027 / 500000) ∧
    -Real.log (66027 / 500000) ≤ (2024544351 / 1000000000) := by
  have h := checkLog_sound (w := (58973 / 191027)) (n := 12)
    (lo := (159562497 / 250000000)) (hi := (638249989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 66027) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 66027) = 1/(66027 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2024544351 / 1000000000) (-506136087 / 250000000) (Real.log (66027 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (625941639 / 1000000000) ≤ -Real.log (500000 / 935003) ∧
    -Real.log (500000 / 935003) ≤ (15648541 / 25000000) := by
  have h := checkLog_sound (w := (435003 / 1435003)) (n := 12)
    (lo := (625941639 / 1000000000)) (hi := (15648541 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((935003 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(935003 / 500000) = 1/(500000 / 935003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (625941639 / 1000000000) (15648541 / 25000000) (Real.log (935003 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (935003 / 500000) = -Real.log (500000 / 935003) := by
    rw [show ((935003 / 500000) : ℝ) = ((500000 / 935003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1020133491 / 500000000) ≤ -Real.log (64997 / 500000) ∧
    -Real.log (64997 / 500000) ≤ (408053397 / 200000000) := by
  have h := checkLog_sound (w := (60003 / 189997)) (n := 12)
    (lo := (326986311 / 500000000)) (hi := (653972623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 64997) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 64997) = 1/(64997 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-408053397 / 200000000) (-1020133491 / 500000000) (Real.log (64997 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2723315499 / 1000000000) ≤ -Real.log (250000000000 / 3807684036259) ∧
    -Real.log (250000000000 / 3807684036259) ≤ (2723315503 / 1000000000) := by
  have h := checkLog_sound (w := (1807684036259 / 5807684036259)) (n := 12)
    (lo := (643873959 / 1000000000)) (hi := (16096849 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3807684036259 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3807684036259 / 2000000000000) = 1/(250000000000 / 3807684036259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2723315499 / 1000000000) (2723315503 / 1000000000) (Real.log (3807684036259 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3807684036259 / 250000000000) = -Real.log (250000000000 / 3807684036259) := by
    rw [show ((3807684036259 / 250000000000) : ℝ) = ((250000000000 / 3807684036259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1369069679 / 500000000) ≤ -Real.log (10000000000 / 154581961817) ∧
    -Real.log (10000000000 / 154581961817) ≤ (1369069681 / 500000000) := by
  have h := checkLog_sound (w := (74581961817 / 234581961817)) (n := 12)
    (lo := (329348909 / 500000000)) (hi := (658697819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154581961817 / 80000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(154581961817 / 80000000000) = 1/(10000000000 / 154581961817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1369069679 / 500000000) (1369069681 / 500000000) (Real.log (154581961817 / 10000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (154581961817 / 10000000000) = -Real.log (10000000000 / 154581961817) := by
    rw [show ((154581961817 / 10000000000) : ℝ) = ((10000000000 / 154581961817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1324691889 / 500000000) ≤ -Real.log (500000000000 / 7072659669529) ∧
    -Real.log (500000000000 / 7072659669529) ≤ (1324691891 / 500000000) := by
  have h := checkLog_sound (w := (3072659669529 / 11072659669529)) (n := 12)
    (lo := (284971119 / 500000000)) (hi := (569942239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7072659669529 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7072659669529 / 4000000000000) = 1/(500000000000 / 7072659669529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1324691889 / 500000000) (1324691891 / 500000000) (Real.log (7072659669529 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7072659669529 / 500000000000) = -Real.log (500000000000 / 7072659669529) := by
    rw [show ((7072659669529 / 500000000000) : ℝ) = ((500000000000 / 7072659669529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2666208621 / 1000000000) ≤ -Real.log (500000000000 / 7192662738281) ∧
    -Real.log (500000000000 / 7192662738281) ≤ (21329669 / 8000000) := by
  have h := checkLog_sound (w := (3192662738281 / 11192662738281)) (n := 12)
    (lo := (586767081 / 1000000000)) (hi := (293383541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7192662738281 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7192662738281 / 4000000000000) = 1/(500000000000 / 7192662738281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2666208621 / 1000000000) (21329669 / 8000000) (Real.log (7192662738281 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7192662738281 / 500000000000) = -Real.log (500000000000 / 7192662738281) := by
    rw [show ((7192662738281 / 500000000000) : ℝ) = ((500000000000 / 7192662738281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0194
