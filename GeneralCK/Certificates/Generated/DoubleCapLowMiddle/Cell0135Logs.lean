import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0135
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

theorem reflection_log_1_neg : (132069909 / 200000000) ≤ -Real.log (6400 / 12387) ∧
    -Real.log (6400 / 12387) ≤ (330174773 / 500000000) := by
  have h := checkLog_sound (w := (5987 / 18787)) (n := 12)
    (lo := (132069909 / 200000000)) (hi := (330174773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12387 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12387 / 6400) = 1/(6400 / 12387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (132069909 / 200000000) (330174773 / 500000000) (Real.log (12387 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12387 / 6400) = -Real.log (6400 / 12387) := by
    rw [show ((12387 / 6400) : ℝ) = ((6400 / 12387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1370302837 / 500000000) ≤ -Real.log (413 / 6400) ∧
    -Real.log (413 / 6400) ≤ (1370302839 / 500000000) := by
  have h := checkLog_sound (w := (387 / 1213)) (n := 12)
    (lo := (330582067 / 500000000)) (hi := (132232827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 413) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 413) = 1/(413 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1370302839 / 500000000) (-1370302837 / 500000000) (Real.log (413 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (131993201 / 200000000) ≤ -Real.log (25600 / 49529) ∧
    -Real.log (25600 / 49529) ≤ (329983003 / 500000000) := by
  have h := checkLog_sound (w := (23929 / 75129)) (n := 12)
    (lo := (131993201 / 200000000)) (hi := (329983003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49529 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49529 / 25600) = 1/(25600 / 49529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (131993201 / 200000000) (329983003 / 500000000) (Real.log (49529 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49529 / 25600) = -Real.log (25600 / 49529) := by
    rw [show ((49529 / 25600) : ℝ) = ((25600 / 49529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (27291701 / 10000000) ≤ -Real.log (1671 / 25600) ∧
    -Real.log (1671 / 25600) ≤ (341146263 / 125000000) := by
  have h := checkLog_sound (w := (1529 / 4871)) (n := 12)
    (lo := (8121607 / 12500000)) (hi := (649728561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1671) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1671) = 1/(1671 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-341146263 / 125000000) (-27291701 / 10000000) (Real.log (1671 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (313219821 / 500000000) ≤ -Real.log (3200 / 5987) ∧
    -Real.log (3200 / 5987) ≤ (626439643 / 1000000000) := by
  have h := checkLog_sound (w := (2787 / 9187)) (n := 12)
    (lo := (313219821 / 500000000)) (hi := (626439643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5987 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5987 / 3200) = 1/(3200 / 5987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (313219821 / 500000000) (626439643 / 1000000000) (Real.log (5987 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5987 / 3200) = -Real.log (3200 / 5987) := by
    rw [show ((5987 / 3200) : ℝ) = ((3200 / 5987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1023729247 / 500000000) ≤ -Real.log (413 / 3200) ∧
    -Real.log (413 / 3200) ≤ (2047458497 / 1000000000) := by
  have h := checkLog_sound (w := (387 / 1213)) (n := 12)
    (lo := (330582067 / 500000000)) (hi := (132232827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 413) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 413) = 1/(413 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2047458497 / 1000000000) (-1023729247 / 500000000) (Real.log (413 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (625645941 / 1000000000) ≤ -Real.log (12800 / 23929) ∧
    -Real.log (12800 / 23929) ≤ (312822971 / 500000000) := by
  have h := checkLog_sound (w := (11129 / 36729)) (n := 12)
    (lo := (625645941 / 1000000000)) (hi := (312822971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23929 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23929 / 12800) = 1/(12800 / 23929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (625645941 / 1000000000) (312822971 / 500000000) (Real.log (23929 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23929 / 12800) = -Real.log (12800 / 23929) := by
    rw [show ((23929 / 12800) : ℝ) = ((12800 / 23929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (50900573 / 25000000) ≤ -Real.log (1671 / 12800) ∧
    -Real.log (1671 / 12800) ≤ (2036022923 / 1000000000) := by
  have h := checkLog_sound (w := (1529 / 4871)) (n := 12)
    (lo := (8121607 / 12500000)) (hi := (649728561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1671) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1671) = 1/(1671 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2036022923 / 1000000000) (-50900573 / 25000000) (Real.log (1671 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (666783697 / 1000000000) ≤ -Real.log (500000 / 973981) ∧
    -Real.log (500000 / 973981) ≤ (333391849 / 500000000) := by
  have h := checkLog_sound (w := (473981 / 1473981)) (n := 12)
    (lo := (666783697 / 1000000000)) (hi := (333391849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((973981 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(973981 / 500000) = 1/(500000 / 973981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (666783697 / 1000000000) (333391849 / 500000000) (Real.log (973981 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (973981 / 500000) = -Real.log (500000 / 973981) := by
    rw [show ((973981 / 500000) : ℝ) = ((500000 / 973981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (591156211 / 200000000) ≤ -Real.log (26019 / 500000) ∧
    -Real.log (26019 / 500000) ≤ (147789053 / 50000000) := by
  have h := checkLog_sound (w := (5231 / 57269)) (n := 12)
    (lo := (36638467 / 200000000)) (hi := (11449521 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26019) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 26019) = 1/(26019 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-147789053 / 50000000) (-591156211 / 200000000) (Real.log (26019 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (667063951 / 1000000000) ≤ -Real.log (250000 / 487127) ∧
    -Real.log (250000 / 487127) ≤ (41691497 / 62500000) := by
  have h := checkLog_sound (w := (237127 / 737127)) (n := 12)
    (lo := (667063951 / 1000000000)) (hi := (41691497 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487127 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487127 / 250000) = 1/(250000 / 487127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (667063951 / 1000000000) (41691497 / 62500000) (Real.log (487127 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (487127 / 250000) = -Real.log (250000 / 487127) := by
    rw [show ((487127 / 250000) : ℝ) = ((250000 / 487127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (148316441 / 50000000) ≤ -Real.log (12873 / 250000) ∧
    -Real.log (12873 / 250000) ≤ (118653153 / 40000000) := by
  have h := checkLog_sound (w := (1376 / 14249)) (n := 12)
    (lo := (1937401 / 10000000)) (hi := (193740101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12873) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 12873) = 1/(12873 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-118653153 / 40000000) (-148316441 / 50000000) (Real.log (12873 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (6663303 / 10000000) ≤ -Real.log (1000000 / 1947079) ∧
    -Real.log (1000000 / 1947079) ≤ (666330301 / 1000000000) := by
  have h := checkLog_sound (w := (947079 / 2947079)) (n := 12)
    (lo := (6663303 / 10000000)) (hi := (666330301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1947079 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1947079 / 1000000) = 1/(1000000 / 1947079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (6663303 / 10000000) (666330301 / 1000000000) (Real.log (1947079 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1947079 / 1000000) = -Real.log (1000000 / 1947079) := by
    rw [show ((1947079 / 1000000) : ℝ) = ((1000000 / 1947079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2938955041 / 1000000000) ≤ -Real.log (52921 / 1000000) ∧
    -Real.log (52921 / 1000000) ≤ (1469477523 / 500000000) := by
  have h := checkLog_sound (w := (9579 / 115421)) (n := 12)
    (lo := (166366321 / 1000000000)) (hi := (83183161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 52921) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 52921) = 1/(52921 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1469477523 / 500000000) (-2938955041 / 1000000000) (Real.log (52921 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (166655751 / 250000000) ≤ -Real.log (1000000 / 1947649) ∧
    -Real.log (1000000 / 1947649) ≤ (133324601 / 200000000) := by
  have h := checkLog_sound (w := (947649 / 2947649)) (n := 12)
    (lo := (166655751 / 250000000)) (hi := (133324601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1947649 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1947649 / 1000000) = 1/(1000000 / 1947649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (166655751 / 250000000) (133324601 / 200000000) (Real.log (1947649 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1947649 / 1000000) = -Real.log (1000000 / 1947649) := by
    rw [show ((1947649 / 1000000) : ℝ) = ((1000000 / 1947649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2949784237 / 1000000000) ≤ -Real.log (52351 / 1000000) ∧
    -Real.log (52351 / 1000000) ≤ (1474892121 / 500000000) := by
  have h := checkLog_sound (w := (10149 / 114851)) (n := 12)
    (lo := (177195517 / 1000000000)) (hi := (88597759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 52351) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 52351) = 1/(52351 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1474892121 / 500000000) (-2949784237 / 1000000000) (Real.log (52351 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3622564753 / 1000000000) ≤ -Real.log (250000000000 / 9358363119259) ∧
    -Real.log (250000000000 / 9358363119259) ≤ (3622564759 / 1000000000) := by
  have h := checkLog_sound (w := (1358363119259 / 17358363119259)) (n := 12)
    (lo := (156828853 / 1000000000)) (hi := (78414427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9358363119259 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9358363119259 / 8000000000000) = 1/(250000000000 / 9358363119259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3622564753 / 1000000000) (3622564759 / 1000000000) (Real.log (9358363119259 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9358363119259 / 250000000000) = -Real.log (250000000000 / 9358363119259) := by
    rw [show ((9358363119259 / 250000000000) : ℝ) = ((250000000000 / 9358363119259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3633392771 / 1000000000) ≤ -Real.log (50000000000 / 1892049250369) ∧
    -Real.log (50000000000 / 1892049250369) ≤ (3633392777 / 1000000000) := by
  have h := checkLog_sound (w := (292049250369 / 3492049250369)) (n := 12)
    (lo := (167656871 / 1000000000)) (hi := (20957109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1892049250369 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1892049250369 / 1600000000000) = 1/(50000000000 / 1892049250369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3633392771 / 1000000000) (3633392777 / 1000000000) (Real.log (1892049250369 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1892049250369 / 50000000000) = -Real.log (50000000000 / 1892049250369) := by
    rw [show ((1892049250369 / 50000000000) : ℝ) = ((50000000000 / 1892049250369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3605285341 / 1000000000) ≤ -Real.log (31250000000 / 1149755649931) ∧
    -Real.log (31250000000 / 1149755649931) ≤ (3605285347 / 1000000000) := by
  have h := checkLog_sound (w := (149755649931 / 2149755649931)) (n := 12)
    (lo := (139549441 / 1000000000)) (hi := (69774721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1149755649931 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1149755649931 / 1000000000000) = 1/(31250000000 / 1149755649931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3605285341 / 1000000000) (3605285347 / 1000000000) (Real.log (1149755649931 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1149755649931 / 31250000000) = -Real.log (31250000000 / 1149755649931) := by
    rw [show ((1149755649931 / 31250000000) : ℝ) = ((31250000000 / 1149755649931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3616407241 / 1000000000) ≤ -Real.log (125000000000 / 4650457966419) ∧
    -Real.log (125000000000 / 4650457966419) ≤ (3616407247 / 1000000000) := by
  have h := checkLog_sound (w := (650457966419 / 8650457966419)) (n := 12)
    (lo := (150671341 / 1000000000)) (hi := (75335671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4650457966419 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4650457966419 / 4000000000000) = 1/(125000000000 / 4650457966419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3616407241 / 1000000000) (3616407247 / 1000000000) (Real.log (4650457966419 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4650457966419 / 125000000000) = -Real.log (125000000000 / 4650457966419) := by
    rw [show ((4650457966419 / 125000000000) : ℝ) = ((125000000000 / 4650457966419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0135
