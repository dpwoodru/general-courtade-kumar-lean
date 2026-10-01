import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0461
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

theorem reflection_log_1_neg : (92745179 / 500000000) ≤ -Real.log (10240 / 12327) ∧
    -Real.log (10240 / 12327) ≤ (185490359 / 1000000000) := by
  have h := checkLog_sound (w := (2087 / 22567)) (n := 12)
    (lo := (92745179 / 500000000)) (hi := (185490359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12327 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12327 / 10240) = 1/(10240 / 12327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (92745179 / 500000000) (185490359 / 1000000000) (Real.log (12327 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12327 / 10240) = -Real.log (10240 / 12327) := by
    rw [show ((12327 / 10240) : ℝ) = ((10240 / 12327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (227915661 / 1000000000) ≤ -Real.log (8153 / 10240) ∧
    -Real.log (8153 / 10240) ≤ (113957831 / 500000000) := by
  have h := checkLog_sound (w := (2087 / 18393)) (n := 12)
    (lo := (227915661 / 1000000000)) (hi := (113957831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8153) = 1/(8153 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-113957831 / 500000000) (-227915661 / 1000000000) (Real.log (8153 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (185246961 / 1000000000) ≤ -Real.log (2560 / 3081) ∧
    -Real.log (2560 / 3081) ≤ (92623481 / 500000000) := by
  have h := checkLog_sound (w := (521 / 5641)) (n := 12)
    (lo := (185246961 / 1000000000)) (hi := (92623481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3081 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3081 / 2560) = 1/(2560 / 3081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (185246961 / 1000000000) (92623481 / 500000000) (Real.log (3081 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3081 / 2560) = -Real.log (2560 / 3081) := by
    rw [show ((3081 / 2560) : ℝ) = ((2560 / 3081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (113773883 / 500000000) ≤ -Real.log (2039 / 2560) ∧
    -Real.log (2039 / 2560) ≤ (227547767 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 4599)) (n := 12)
    (lo := (113773883 / 500000000)) (hi := (227547767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2039) = 1/(2039 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-227547767 / 1000000000) (-113773883 / 500000000) (Real.log (2039 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (10684323 / 31250000) ≤ -Real.log (5120 / 7207) ∧
    -Real.log (5120 / 7207) ≤ (341898337 / 1000000000) := by
  have h := checkLog_sound (w := (2087 / 12327)) (n := 12)
    (lo := (10684323 / 31250000)) (hi := (341898337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7207 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7207 / 5120) = 1/(5120 / 7207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (10684323 / 31250000) (341898337 / 1000000000) (Real.log (7207 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7207 / 5120) = -Real.log (5120 / 7207) := by
    rw [show ((7207 / 5120) : ℝ) = ((5120 / 7207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (52360221 / 100000000) ≤ -Real.log (3033 / 5120) ∧
    -Real.log (3033 / 5120) ≤ (523602211 / 1000000000) := by
  have h := checkLog_sound (w := (2087 / 8153)) (n := 12)
    (lo := (52360221 / 100000000)) (hi := (523602211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3033) = 1/(3033 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-523602211 / 1000000000) (-52360221 / 100000000) (Real.log (3033 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (85370497 / 250000000) ≤ -Real.log (1280 / 1801) ∧
    -Real.log (1280 / 1801) ≤ (341481989 / 1000000000) := by
  have h := checkLog_sound (w := (521 / 3081)) (n := 12)
    (lo := (85370497 / 250000000)) (hi := (341481989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1801 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1801 / 1280) = 1/(1280 / 1801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (85370497 / 250000000) (341481989 / 1000000000) (Real.log (1801 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1801 / 1280) = -Real.log (1280 / 1801) := by
    rw [show ((1801 / 1280) : ℝ) = ((1280 / 1801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (522613579 / 1000000000) ≤ -Real.log (759 / 1280) ∧
    -Real.log (759 / 1280) ≤ (26130679 / 50000000) := by
  have h := checkLog_sound (w := (521 / 2039)) (n := 12)
    (lo := (522613579 / 1000000000)) (hi := (26130679 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 759) = 1/(759 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-26130679 / 50000000) (-522613579 / 1000000000) (Real.log (759 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (254604233 / 1000000000) ≤ -Real.log (1000000 / 1289951) ∧
    -Real.log (1000000 / 1289951) ≤ (127302117 / 500000000) := by
  have h := checkLog_sound (w := (289951 / 2289951)) (n := 12)
    (lo := (254604233 / 1000000000)) (hi := (127302117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1289951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1289951 / 1000000) = 1/(1000000 / 1289951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (254604233 / 1000000000) (127302117 / 500000000) (Real.log (1289951 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1289951 / 1000000) = -Real.log (1000000 / 1289951) := by
    rw [show ((1289951 / 1000000) : ℝ) = ((1000000 / 1289951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (342421297 / 1000000000) ≤ -Real.log (710049 / 1000000) ∧
    -Real.log (710049 / 1000000) ≤ (171210649 / 500000000) := by
  have h := checkLog_sound (w := (289951 / 1710049)) (n := 12)
    (lo := (342421297 / 1000000000)) (hi := (171210649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 710049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 710049) = 1/(710049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-171210649 / 500000000) (-342421297 / 1000000000) (Real.log (710049 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (15933353 / 62500000) ≤ -Real.log (125000 / 161297) ∧
    -Real.log (125000 / 161297) ≤ (254933649 / 1000000000) := by
  have h := checkLog_sound (w := (36297 / 286297)) (n := 12)
    (lo := (15933353 / 62500000)) (hi := (254933649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161297 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161297 / 125000) = 1/(125000 / 161297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (15933353 / 62500000) (254933649 / 1000000000) (Real.log (161297 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (161297 / 125000) = -Real.log (125000 / 161297) := by
    rw [show ((161297 / 125000) : ℝ) = ((125000 / 161297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (171510013 / 500000000) ≤ -Real.log (88703 / 125000) ∧
    -Real.log (88703 / 125000) ≤ (343020027 / 1000000000) := by
  have h := checkLog_sound (w := (36297 / 213703)) (n := 12)
    (lo := (171510013 / 500000000)) (hi := (343020027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88703) = 1/(88703 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-343020027 / 1000000000) (-171510013 / 500000000) (Real.log (88703 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23818557 / 125000000) ≤ -Real.log (1000000 / 1209913) ∧
    -Real.log (1000000 / 1209913) ≤ (190548457 / 1000000000) := by
  have h := checkLog_sound (w := (209913 / 2209913)) (n := 12)
    (lo := (23818557 / 125000000)) (hi := (190548457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1209913 / 1000000) = 1/(1000000 / 1209913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23818557 / 125000000) (190548457 / 1000000000) (Real.log (1209913 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1209913 / 1000000) = -Real.log (1000000 / 1209913) := by
    rw [show ((1209913 / 1000000) : ℝ) = ((1000000 / 1209913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (235612213 / 1000000000) ≤ -Real.log (790087 / 1000000) ∧
    -Real.log (790087 / 1000000) ≤ (117806107 / 500000000) := by
  have h := checkLog_sound (w := (209913 / 1790087)) (n := 12)
    (lo := (235612213 / 1000000000)) (hi := (117806107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 790087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 790087) = 1/(790087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-117806107 / 500000000) (-235612213 / 1000000000) (Real.log (790087 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (38162911 / 200000000) ≤ -Real.log (200000 / 242047) ∧
    -Real.log (200000 / 242047) ≤ (47703639 / 250000000) := by
  have h := checkLog_sound (w := (42047 / 442047)) (n := 12)
    (lo := (38162911 / 200000000)) (hi := (47703639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242047 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242047 / 200000) = 1/(200000 / 242047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (38162911 / 200000000) (47703639 / 250000000) (Real.log (242047 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (242047 / 200000) = -Real.log (200000 / 242047) := by
    rw [show ((242047 / 200000) : ℝ) = ((200000 / 242047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (118009923 / 500000000) ≤ -Real.log (157953 / 200000) ∧
    -Real.log (157953 / 200000) ≤ (236019847 / 1000000000) := by
  have h := checkLog_sound (w := (42047 / 357953)) (n := 12)
    (lo := (118009923 / 500000000)) (hi := (236019847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 157953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 157953) = 1/(157953 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-236019847 / 1000000000) (-118009923 / 500000000) (Real.log (157953 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (59702553 / 100000000) ≤ -Real.log (500000000000 / 908353507997) ∧
    -Real.log (500000000000 / 908353507997) ≤ (597025531 / 1000000000) := by
  have h := checkLog_sound (w := (408353507997 / 1408353507997)) (n := 12)
    (lo := (59702553 / 100000000)) (hi := (597025531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((908353507997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(908353507997 / 500000000000) = 1/(500000000000 / 908353507997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (59702553 / 100000000) (597025531 / 1000000000) (Real.log (908353507997 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (908353507997 / 500000000000) = -Real.log (500000000000 / 908353507997) := by
    rw [show ((908353507997 / 500000000000) : ℝ) = ((500000000000 / 908353507997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (23918147 / 40000000) ≤ -Real.log (62500000000 / 113649622899) ∧
    -Real.log (62500000000 / 113649622899) ≤ (149488419 / 250000000) := by
  have h := checkLog_sound (w := (51149622899 / 176149622899)) (n := 12)
    (lo := (23918147 / 40000000)) (hi := (149488419 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113649622899 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113649622899 / 62500000000) = 1/(62500000000 / 113649622899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (23918147 / 40000000) (149488419 / 250000000) (Real.log (113649622899 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (113649622899 / 62500000000) = -Real.log (62500000000 / 113649622899) := by
    rw [show ((113649622899 / 62500000000) : ℝ) = ((62500000000 / 113649622899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (426160669 / 1000000000) ≤ -Real.log (500000000000 / 765683399423) ∧
    -Real.log (500000000000 / 765683399423) ≤ (42616067 / 100000000) := by
  have h := checkLog_sound (w := (265683399423 / 1265683399423)) (n := 12)
    (lo := (426160669 / 1000000000)) (hi := (42616067 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((765683399423 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(765683399423 / 500000000000) = 1/(500000000000 / 765683399423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (426160669 / 1000000000) (42616067 / 100000000) (Real.log (765683399423 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (765683399423 / 500000000000) = -Real.log (500000000000 / 765683399423) := by
    rw [show ((765683399423 / 500000000000) : ℝ) = ((500000000000 / 765683399423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (426834401 / 1000000000) ≤ -Real.log (250000000000 / 383099719537) ∧
    -Real.log (250000000000 / 383099719537) ≤ (213417201 / 500000000) := by
  have h := checkLog_sound (w := (133099719537 / 633099719537)) (n := 12)
    (lo := (426834401 / 1000000000)) (hi := (213417201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383099719537 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383099719537 / 250000000000) = 1/(250000000000 / 383099719537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (426834401 / 1000000000) (213417201 / 500000000) (Real.log (383099719537 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (383099719537 / 250000000000) = -Real.log (250000000000 / 383099719537) := by
    rw [show ((383099719537 / 250000000000) : ℝ) = ((250000000000 / 383099719537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0461
