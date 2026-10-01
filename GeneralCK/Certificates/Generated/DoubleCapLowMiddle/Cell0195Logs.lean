import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0195
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

theorem reflection_log_1_neg : (300961197 / 500000000) ≤ -Real.log (1600 / 2921) ∧
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


theorem reflection_log_1 : Bounds (300961197 / 500000000) (120384479 / 200000000) (Real.log (2921 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2921 / 1600) = -Real.log (1600 / 2921) := by
    rw [show ((2921 / 1600) : ℝ) = ((1600 / 2921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (13972377 / 8000000) ≤ -Real.log (279 / 1600) ∧
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


theorem reflection_log_2 : Bounds (-218318391 / 125000000) (-13972377 / 8000000) (Real.log (279 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (120058983 / 200000000) ≤ -Real.log (1280 / 2333) ∧
    -Real.log (1280 / 2333) ≤ (150073729 / 250000000) := by
  have h := checkLog_sound (w := (1053 / 3613)) (n := 12)
    (lo := (120058983 / 200000000)) (hi := (150073729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2333 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2333 / 1280) = 1/(1280 / 2333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (120058983 / 200000000) (150073729 / 250000000) (Real.log (2333 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2333 / 1280) = -Real.log (1280 / 2333) := by
    rw [show ((2333 / 1280) : ℝ) = ((1280 / 2333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (864832669 / 500000000) ≤ -Real.log (227 / 1280) ∧
    -Real.log (227 / 1280) ≤ (1729665341 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 547)) (n := 12)
    (lo := (171685489 / 500000000)) (hi := (343370979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 227) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 227) = 1/(227 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1729665341 / 1000000000) (-864832669 / 500000000) (Real.log (227 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (15672893 / 31250000) ≤ -Real.log (800 / 1321) ∧
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


theorem reflection_log_5 : Bounds (15672893 / 31250000) (501532577 / 1000000000) (Real.log (1321 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1321 / 800) = -Real.log (800 / 1321) := by
    rw [show ((1321 / 800) : ℝ) = ((800 / 1321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (210679989 / 200000000) ≤ -Real.log (279 / 800) ∧
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


theorem reflection_log_6 : Bounds (-1053399947 / 1000000000) (-210679989 / 200000000) (Real.log (279 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (99586067 / 200000000) ≤ -Real.log (640 / 1053) ∧
    -Real.log (640 / 1053) ≤ (15560323 / 31250000) := by
  have h := checkLog_sound (w := (413 / 1693)) (n := 12)
    (lo := (99586067 / 200000000)) (hi := (15560323 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1053 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1053 / 640) = 1/(640 / 1053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (99586067 / 200000000) (15560323 / 31250000) (Real.log (1053 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1053 / 640) = -Real.log (640 / 1053) := by
    rw [show ((1053 / 640) : ℝ) = ((640 / 1053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (518259079 / 500000000) ≤ -Real.log (227 / 640) ∧
    -Real.log (227 / 640) ≤ (12956477 / 12500000) := by
  have h := checkLog_sound (w := (93 / 547)) (n := 12)
    (lo := (171685489 / 500000000)) (hi := (343370979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 227) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 227) = 1/(227 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12956477 / 12500000) (-518259079 / 500000000) (Real.log (227 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (157164031 / 250000000) ≤ -Real.log (1000000 / 1875089) ∧
    -Real.log (1000000 / 1875089) ≤ (5029249 / 8000000) := by
  have h := checkLog_sound (w := (875089 / 2875089)) (n := 12)
    (lo := (157164031 / 250000000)) (hi := (5029249 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1875089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1875089 / 1000000) = 1/(1000000 / 1875089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (157164031 / 250000000) (5029249 / 8000000) (Real.log (1875089 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1875089 / 1000000) = -Real.log (1000000 / 1875089) := by
    rw [show ((1875089 / 1000000) : ℝ) = ((1000000 / 1875089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2080153793 / 1000000000) ≤ -Real.log (124911 / 1000000) ∧
    -Real.log (124911 / 1000000) ≤ (2080153797 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 249911)) (n := 12)
    (lo := (712253 / 1000000000)) (hi := (356127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124911) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 124911) = 1/(124911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2080153797 / 1000000000) (-2080153793 / 1000000000) (Real.log (124911 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (157389119 / 250000000) ≤ -Real.log (500000 / 938389) ∧
    -Real.log (500000 / 938389) ≤ (629556477 / 1000000000) := by
  have h := checkLog_sound (w := (438389 / 1438389)) (n := 12)
    (lo := (157389119 / 250000000)) (hi := (629556477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((938389 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(938389 / 500000) = 1/(500000 / 938389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (157389119 / 250000000) (629556477 / 1000000000) (Real.log (938389 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (938389 / 500000) = -Real.log (500000 / 938389) := by
    rw [show ((938389 / 500000) : ℝ) = ((500000 / 938389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (209376767 / 100000000) ≤ -Real.log (61611 / 500000) ∧
    -Real.log (61611 / 500000) ≤ (1046883837 / 500000000) := by
  have h := checkLog_sound (w := (889 / 124111)) (n := 12)
    (lo := (1432613 / 100000000)) (hi := (14326131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 61611) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 61611) = 1/(61611 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1046883837 / 500000000) (-209376767 / 100000000) (Real.log (61611 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (311869343 / 500000000) ≤ -Real.log (1000000 / 1865891) ∧
    -Real.log (1000000 / 1865891) ≤ (9745917 / 15625000) := by
  have h := checkLog_sound (w := (865891 / 2865891)) (n := 12)
    (lo := (311869343 / 500000000)) (hi := (9745917 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1865891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1865891 / 1000000) = 1/(1000000 / 1865891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (311869343 / 500000000) (9745917 / 15625000) (Real.log (1865891 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1865891 / 1000000) = -Real.log (1000000 / 1865891) := by
    rw [show ((1865891 / 1000000) : ℝ) = ((1000000 / 1865891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (16072819 / 8000000) ≤ -Real.log (134109 / 1000000) ∧
    -Real.log (134109 / 1000000) ≤ (1004551189 / 500000000) := by
  have h := checkLog_sound (w := (115891 / 384109)) (n := 12)
    (lo := (124561603 / 200000000)) (hi := (38925501 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 134109) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 134109) = 1/(134109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1004551189 / 500000000) (-16072819 / 8000000) (Real.log (134109 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (312419983 / 500000000) ≤ -Real.log (1000000 / 1867947) ∧
    -Real.log (1000000 / 1867947) ≤ (624839967 / 1000000000) := by
  have h := checkLog_sound (w := (867947 / 2867947)) (n := 12)
    (lo := (312419983 / 500000000)) (hi := (624839967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1867947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1867947 / 1000000) = 1/(1000000 / 1867947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (312419983 / 500000000) (624839967 / 1000000000) (Real.log (1867947 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1867947 / 1000000) = -Real.log (1000000 / 1867947) := by
    rw [show ((1867947 / 1000000) : ℝ) = ((1000000 / 1867947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (25306899 / 12500000) ≤ -Real.log (132053 / 1000000) ∧
    -Real.log (132053 / 1000000) ≤ (2024551923 / 1000000000) := by
  have h := checkLog_sound (w := (117947 / 382053)) (n := 12)
    (lo := (15956439 / 25000000)) (hi := (638257561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 132053) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 132053) = 1/(132053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2024551923 / 1000000000) (-25306899 / 12500000) (Real.log (132053 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1354404959 / 500000000) ≤ -Real.log (500000000000 / 7505700058441) ∧
    -Real.log (500000000000 / 7505700058441) ≤ (1354404961 / 500000000) := by
  have h := checkLog_sound (w := (3505700058441 / 11505700058441)) (n := 12)
    (lo := (314684189 / 500000000)) (hi := (629368379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7505700058441 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7505700058441 / 4000000000000) = 1/(500000000000 / 7505700058441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1354404959 / 500000000) (1354404961 / 500000000) (Real.log (7505700058441 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7505700058441 / 500000000000) = -Real.log (500000000000 / 7505700058441) := by
    rw [show ((7505700058441 / 500000000000) : ℝ) = ((500000000000 / 7505700058441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2723324147 / 1000000000) ≤ -Real.log (500000000000 / 7615433932253) ∧
    -Real.log (500000000000 / 7615433932253) ≤ (2723324151 / 1000000000) := by
  have h := checkLog_sound (w := (3615433932253 / 11615433932253)) (n := 12)
    (lo := (643882607 / 1000000000)) (hi := (40242663 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7615433932253 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7615433932253 / 4000000000000) = 1/(500000000000 / 7615433932253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2723324147 / 1000000000) (2723324151 / 1000000000) (Real.log (7615433932253 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7615433932253 / 500000000000) = -Real.log (500000000000 / 7615433932253) := by
    rw [show ((7615433932253 / 500000000000) : ℝ) = ((500000000000 / 7615433932253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1316420531 / 500000000) ≤ -Real.log (500000000000 / 6956621106711) ∧
    -Real.log (500000000000 / 6956621106711) ≤ (1316420533 / 500000000) := by
  have h := checkLog_sound (w := (2956621106711 / 10956621106711)) (n := 12)
    (lo := (276699761 / 500000000)) (hi := (553399523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6956621106711 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6956621106711 / 4000000000000) = 1/(500000000000 / 6956621106711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1316420531 / 500000000) (1316420533 / 500000000) (Real.log (6956621106711 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6956621106711 / 500000000000) = -Real.log (500000000000 / 6956621106711) := by
    rw [show ((6956621106711 / 500000000000) : ℝ) = ((500000000000 / 6956621106711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1324695943 / 500000000) ≤ -Real.log (250000000000 / 3536358507569) ∧
    -Real.log (250000000000 / 3536358507569) ≤ (264939189 / 100000000) := by
  have h := checkLog_sound (w := (1536358507569 / 5536358507569)) (n := 12)
    (lo := (284975173 / 500000000)) (hi := (569950347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3536358507569 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3536358507569 / 2000000000000) = 1/(250000000000 / 3536358507569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1324695943 / 500000000) (264939189 / 100000000) (Real.log (3536358507569 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3536358507569 / 250000000000) = -Real.log (250000000000 / 3536358507569) := by
    rw [show ((3536358507569 / 250000000000) : ℝ) = ((250000000000 / 3536358507569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0195
