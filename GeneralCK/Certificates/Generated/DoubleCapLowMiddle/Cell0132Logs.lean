import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0132
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

theorem reflection_log_1_neg : (661499283 / 1000000000) ≤ -Real.log (5120 / 9921) ∧
    -Real.log (5120 / 9921) ≤ (165374821 / 250000000) := by
  have h := checkLog_sound (w := (4801 / 15041)) (n := 12)
    (lo := (661499283 / 1000000000)) (hi := (165374821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9921 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9921 / 5120) = 1/(5120 / 9921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (661499283 / 1000000000) (165374821 / 250000000) (Real.log (9921 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (9921 / 5120) = -Real.log (5120 / 9921) := by
    rw [show ((9921 / 5120) : ℝ) = ((5120 / 9921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2775718613 / 1000000000) ≤ -Real.log (319 / 5120) ∧
    -Real.log (319 / 5120) ≤ (1387859309 / 500000000) := by
  have h := checkLog_sound (w := (1 / 639)) (n := 12)
    (lo := (3129893 / 1000000000)) (hi := (1564947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 319) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 319) = 1/(319 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1387859309 / 500000000) (-2775718613 / 1000000000) (Real.log (319 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (82639523 / 125000000) ≤ -Real.log (12800 / 24793) ∧
    -Real.log (12800 / 24793) ≤ (132223237 / 200000000) := by
  have h := checkLog_sound (w := (11993 / 37593)) (n := 12)
    (lo := (82639523 / 125000000)) (hi := (132223237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24793 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24793 / 12800) = 1/(12800 / 24793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (82639523 / 125000000) (132223237 / 200000000) (Real.log (24793 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24793 / 12800) = -Real.log (12800 / 24793) := by
    rw [show ((24793 / 12800) : ℝ) = ((12800 / 24793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2763876779 / 1000000000) ≤ -Real.log (807 / 12800) ∧
    -Real.log (807 / 12800) ≤ (2763876783 / 1000000000) := by
  have h := checkLog_sound (w := (793 / 2407)) (n := 12)
    (lo := (684435239 / 1000000000)) (hi := (17110881 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 807) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 807) = 1/(807 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2763876783 / 1000000000) (-2763876779 / 1000000000) (Real.log (807 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (628816971 / 1000000000) ≤ -Real.log (2560 / 4801) ∧
    -Real.log (2560 / 4801) ≤ (157204243 / 250000000) := by
  have h := checkLog_sound (w := (2241 / 7361)) (n := 12)
    (lo := (628816971 / 1000000000)) (hi := (157204243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4801 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4801 / 2560) = 1/(2560 / 4801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (628816971 / 1000000000) (157204243 / 250000000) (Real.log (4801 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4801 / 2560) = -Real.log (2560 / 4801) := by
    rw [show ((4801 / 2560) : ℝ) = ((2560 / 4801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2082571433 / 1000000000) ≤ -Real.log (319 / 2560) ∧
    -Real.log (319 / 2560) ≤ (2082571437 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 639)) (n := 12)
    (lo := (3129893 / 1000000000)) (hi := (1564947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 319) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 319) = 1/(319 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2082571437 / 1000000000) (-2082571433 / 1000000000) (Real.log (319 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (125605031 / 200000000) ≤ -Real.log (6400 / 11993) ∧
    -Real.log (6400 / 11993) ≤ (157006289 / 250000000) := by
  have h := checkLog_sound (w := (5593 / 18393)) (n := 12)
    (lo := (125605031 / 200000000)) (hi := (157006289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11993 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11993 / 6400) = 1/(6400 / 11993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (125605031 / 200000000) (157006289 / 250000000) (Real.log (11993 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11993 / 6400) = -Real.log (6400 / 11993) := by
    rw [show ((11993 / 6400) : ℝ) = ((6400 / 11993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2070729599 / 1000000000) ≤ -Real.log (807 / 6400) ∧
    -Real.log (807 / 6400) ≤ (1035364801 / 500000000) := by
  have h := checkLog_sound (w := (793 / 2407)) (n := 12)
    (lo := (684435239 / 1000000000)) (hi := (17110881 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 807) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 807) = 1/(807 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1035364801 / 500000000) (-2070729599 / 1000000000) (Real.log (807 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (667625249 / 1000000000) ≤ -Real.log (500000 / 974801) ∧
    -Real.log (500000 / 974801) ≤ (2670501 / 4000000) := by
  have h := checkLog_sound (w := (474801 / 1474801)) (n := 12)
    (lo := (667625249 / 1000000000)) (hi := (2670501 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(974801 / 500000) = 1/(500000 / 974801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (667625249 / 1000000000) (2670501 / 4000000) (Real.log (974801 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (974801 / 500000) = -Real.log (500000 / 974801) := by
    rw [show ((974801 / 500000) : ℝ) = ((500000 / 974801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (373475473 / 125000000) ≤ -Real.log (25199 / 500000) ∧
    -Real.log (25199 / 500000) ≤ (2987803789 / 1000000000) := by
  have h := checkLog_sound (w := (6051 / 56449)) (n := 12)
    (lo := (26901883 / 125000000)) (hi := (43043013 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25199) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 25199) = 1/(25199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2987803789 / 1000000000) (-373475473 / 125000000) (Real.log (25199 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (133581361 / 200000000) ≤ -Real.log (1000000 / 1950151) ∧
    -Real.log (1000000 / 1950151) ≤ (333953403 / 500000000) := by
  have h := checkLog_sound (w := (950151 / 2950151)) (n := 12)
    (lo := (133581361 / 200000000)) (hi := (333953403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1950151 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1950151 / 1000000) = 1/(1000000 / 1950151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (133581361 / 200000000) (333953403 / 500000000) (Real.log (1950151 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1950151 / 1000000) = -Real.log (1000000 / 1950151) := by
    rw [show ((1950151 / 1000000) : ℝ) = ((1000000 / 1950151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (74968921 / 25000000) ≤ -Real.log (49849 / 1000000) ∧
    -Real.log (49849 / 1000000) ≤ (599751369 / 200000000) := by
  have h := checkLog_sound (w := (12651 / 112349)) (n := 12)
    (lo := (5654203 / 25000000)) (hi := (226168121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49849) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 49849) = 1/(49849 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-599751369 / 200000000) (-74968921 / 25000000) (Real.log (49849 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (667207127 / 1000000000) ≤ -Real.log (1000000 / 1948787) ∧
    -Real.log (1000000 / 1948787) ≤ (83400891 / 125000000) := by
  have h := checkLog_sound (w := (948787 / 2948787)) (n := 12)
    (lo := (667207127 / 1000000000)) (hi := (83400891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1948787 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1948787 / 1000000) = 1/(1000000 / 1948787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (667207127 / 1000000000) (83400891 / 125000000) (Real.log (1948787 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1948787 / 1000000) = -Real.log (1000000 / 1948787) := by
    rw [show ((1948787 / 1000000) : ℝ) = ((1000000 / 1948787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (297176187 / 100000000) ≤ -Real.log (51213 / 1000000) ∧
    -Real.log (51213 / 1000000) ≤ (4754819 / 1600000) := by
  have h := checkLog_sound (w := (11287 / 113713)) (n := 12)
    (lo := (3983463 / 20000000)) (hi := (199173151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51213) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 51213) = 1/(51213 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4754819 / 1600000) (-297176187 / 100000000) (Real.log (51213 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (667500087 / 1000000000) ≤ -Real.log (500000 / 974679) ∧
    -Real.log (500000 / 974679) ≤ (83437511 / 125000000) := by
  have h := checkLog_sound (w := (474679 / 1474679)) (n := 12)
    (lo := (667500087 / 1000000000)) (hi := (83437511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((974679 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(974679 / 500000) = 1/(500000 / 974679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (667500087 / 1000000000) (83437511 / 125000000) (Real.log (974679 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (974679 / 500000) = -Real.log (500000 / 974679) := by
    rw [show ((974679 / 500000) : ℝ) = ((500000 / 974679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (596594801 / 200000000) ≤ -Real.log (25321 / 500000) ∧
    -Real.log (25321 / 500000) ≤ (298297401 / 100000000) := by
  have h := checkLog_sound (w := (5929 / 56571)) (n := 12)
    (lo := (42077057 / 200000000)) (hi := (105192643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25321) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 25321) = 1/(25321 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-298297401 / 100000000) (-596594801 / 200000000) (Real.log (25321 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3655429033 / 1000000000) ≤ -Real.log (500000000000 / 19342057224493) ∧
    -Real.log (500000000000 / 19342057224493) ≤ (3655429039 / 1000000000) := by
  have h := checkLog_sound (w := (3342057224493 / 35342057224493)) (n := 12)
    (lo := (189693133 / 1000000000)) (hi := (94846567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19342057224493 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19342057224493 / 16000000000000) = 1/(500000000000 / 19342057224493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3655429033 / 1000000000) (3655429039 / 1000000000) (Real.log (19342057224493 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (19342057224493 / 500000000000) = -Real.log (500000000000 / 19342057224493) := by
    rw [show ((19342057224493 / 500000000000) : ℝ) = ((500000000000 / 19342057224493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (733332729 / 200000000) ≤ -Real.log (500000000000 / 19560582960541) ∧
    -Real.log (500000000000 / 19560582960541) ≤ (3666663651 / 1000000000) := by
  have h := checkLog_sound (w := (3560582960541 / 35560582960541)) (n := 12)
    (lo := (40185549 / 200000000)) (hi := (100463873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19560582960541 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19560582960541 / 16000000000000) = 1/(500000000000 / 19560582960541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (733332729 / 200000000) (3666663651 / 1000000000) (Real.log (19560582960541 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (19560582960541 / 500000000000) = -Real.log (500000000000 / 19560582960541) := by
    rw [show ((19560582960541 / 500000000000) : ℝ) = ((500000000000 / 19560582960541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3638968997 / 1000000000) ≤ -Real.log (500000000000 / 19026292152383) ∧
    -Real.log (500000000000 / 19026292152383) ≤ (3638969003 / 1000000000) := by
  have h := checkLog_sound (w := (3026292152383 / 35026292152383)) (n := 12)
    (lo := (173233097 / 1000000000)) (hi := (86616549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19026292152383 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(19026292152383 / 16000000000000) = 1/(500000000000 / 19026292152383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3638968997 / 1000000000) (3638969003 / 1000000000) (Real.log (19026292152383 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (19026292152383 / 500000000000) = -Real.log (500000000000 / 19026292152383) := by
    rw [show ((19026292152383 / 500000000000) : ℝ) = ((500000000000 / 19026292152383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (912618523 / 250000000) ≤ -Real.log (125000000000 / 4811613877809) ∧
    -Real.log (125000000000 / 4811613877809) ≤ (1825237049 / 500000000) := by
  have h := checkLog_sound (w := (811613877809 / 8811613877809)) (n := 12)
    (lo := (11546137 / 62500000)) (hi := (184738193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4811613877809 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4811613877809 / 4000000000000) = 1/(125000000000 / 4811613877809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (912618523 / 250000000) (1825237049 / 500000000) (Real.log (4811613877809 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4811613877809 / 125000000000) = -Real.log (125000000000 / 4811613877809) := by
    rw [show ((4811613877809 / 125000000000) : ℝ) = ((125000000000 / 4811613877809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0132
