import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5056_neg : (22379267 / 250000000) ≤ -Real.log (500000 / 546823) ∧
    -Real.log (500000 / 546823) ≤ (89517069 / 1000000000) := by
  have h := checkLog_sound (w := (46823 / 1046823)) (n := 12)
    (lo := (22379267 / 250000000)) (hi := (89517069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546823 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546823 / 500000) = 1/(500000 / 546823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5056 : Bounds (22379267 / 250000000) (89517069 / 1000000000) (Real.log (546823 / 500000)) := by
  have h := reflection_log_5056_neg
  have he : Real.log (546823 / 500000) = -Real.log (500000 / 546823) := by
    rw [show ((546823 / 500000) : ℝ) = ((500000 / 546823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5057_neg : (2458133 / 25000000) ≤ -Real.log (453177 / 500000) ∧
    -Real.log (453177 / 500000) ≤ (98325321 / 1000000000) := by
  have h := checkLog_sound (w := (46823 / 953177)) (n := 12)
    (lo := (2458133 / 25000000)) (hi := (98325321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453177) = 1/(453177 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5057 : Bounds (-98325321 / 1000000000) (-2458133 / 25000000) (Real.log (453177 / 500000)) := by
  have h := reflection_log_5057_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5058_neg : (89733751 / 1000000000) ≤ -Real.log (1000000 / 1093883) ∧
    -Real.log (1000000 / 1093883) ≤ (11216719 / 125000000) := by
  have h := checkLog_sound (w := (93883 / 2093883)) (n := 12)
    (lo := (89733751 / 1000000000)) (hi := (11216719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093883 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093883 / 1000000) = 1/(1000000 / 1093883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5058 : Bounds (89733751 / 1000000000) (11216719 / 125000000) (Real.log (1093883 / 1000000)) := by
  have h := reflection_log_5058_neg
  have he : Real.log (1093883 / 1000000) = -Real.log (1000000 / 1093883) := by
    rw [show ((1093883 / 1000000) : ℝ) = ((1000000 / 1093883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5059_neg : (49293421 / 500000000) ≤ -Real.log (906117 / 1000000) ∧
    -Real.log (906117 / 1000000) ≤ (98586843 / 1000000000) := by
  have h := checkLog_sound (w := (93883 / 1906117)) (n := 12)
    (lo := (49293421 / 500000000)) (hi := (98586843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906117) = 1/(906117 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5059 : Bounds (-98586843 / 1000000000) (-49293421 / 500000000) (Real.log (906117 / 1000000)) := by
  have h := reflection_log_5059_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5060_neg : (885309 / 100000000) ≤ -Real.log (991185982311 / 1000000000000) ∧
    -Real.log (991185982311 / 1000000000000) ≤ (8853091 / 1000000000) := by
  have h := checkLog_sound (w := (8814017689 / 1991185982311)) (n := 12)
    (lo := (885309 / 100000000)) (hi := (8853091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991185982311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991185982311) = 1/(991185982311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5060 : Bounds (-8853091 / 1000000000) (-885309 / 100000000) (Real.log (991185982311 / 1000000000000)) := by
  have h := reflection_log_5060_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5061_neg : (2202063 / 250000000) ≤ -Real.log (247807606671 / 250000000000) ∧
    -Real.log (247807606671 / 250000000000) ≤ (8808253 / 1000000000) := by
  have h := checkLog_sound (w := (2192393329 / 497807606671)) (n := 12)
    (lo := (2202063 / 250000000)) (hi := (8808253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247807606671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247807606671) = 1/(247807606671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5061 : Bounds (-8808253 / 1000000000) (-2202063 / 250000000) (Real.log (247807606671 / 250000000000)) := by
  have h := reflection_log_5061_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5062_neg : (187842389 / 1000000000) ≤ -Real.log (50000000000 / 60332166019) ∧
    -Real.log (50000000000 / 60332166019) ≤ (18784239 / 100000000) := by
  have h := checkLog_sound (w := (10332166019 / 110332166019)) (n := 12)
    (lo := (187842389 / 1000000000)) (hi := (18784239 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60332166019 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60332166019 / 50000000000) = 1/(50000000000 / 60332166019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5062 : Bounds (187842389 / 1000000000) (18784239 / 100000000) (Real.log (60332166019 / 50000000000)) := by
  have h := reflection_log_5062_neg
  have he : Real.log (60332166019 / 50000000000) = -Real.log (50000000000 / 60332166019) := by
    rw [show ((60332166019 / 50000000000) : ℝ) = ((50000000000 / 60332166019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5063_neg : (188320593 / 1000000000) ≤ -Real.log (500000000000 / 603610240179) ∧
    -Real.log (500000000000 / 603610240179) ≤ (94160297 / 500000000) := by
  have h := checkLog_sound (w := (103610240179 / 1103610240179)) (n := 12)
    (lo := (188320593 / 1000000000)) (hi := (94160297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603610240179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603610240179 / 500000000000) = 1/(500000000000 / 603610240179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5063 : Bounds (188320593 / 1000000000) (94160297 / 500000000) (Real.log (603610240179 / 500000000000)) := by
  have h := reflection_log_5063_neg
  have he : Real.log (603610240179 / 500000000000) = -Real.log (500000000000 / 603610240179) := by
    rw [show ((603610240179 / 500000000000) : ℝ) = ((500000000000 / 603610240179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5064_neg : (1508011 / 4000000) ≤ -Real.log (500000000000 / 728954160009) ∧
    -Real.log (500000000000 / 728954160009) ≤ (377002751 / 1000000000) := by
  have h := checkLog_sound (w := (228954160009 / 1228954160009)) (n := 12)
    (lo := (1508011 / 4000000)) (hi := (377002751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728954160009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728954160009 / 500000000000) = 1/(500000000000 / 728954160009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5064 : Bounds (1508011 / 4000000) (377002751 / 1000000000) (Real.log (728954160009 / 500000000000)) := by
  have h := reflection_log_5064_neg
  have he : Real.log (728954160009 / 500000000000) = -Real.log (500000000000 / 728954160009) := by
    rw [show ((728954160009 / 500000000000) : ℝ) = ((500000000000 / 728954160009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5065_neg : (188604973 / 500000000) ≤ -Real.log (500000000000 / 729105211407) ∧
    -Real.log (500000000000 / 729105211407) ≤ (377209947 / 1000000000) := by
  have h := checkLog_sound (w := (229105211407 / 1229105211407)) (n := 12)
    (lo := (188604973 / 500000000)) (hi := (377209947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729105211407 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729105211407 / 500000000000) = 1/(500000000000 / 729105211407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5065 : Bounds (188604973 / 500000000) (377209947 / 1000000000) (Real.log (729105211407 / 500000000000)) := by
  have h := reflection_log_5065_neg
  have he : Real.log (729105211407 / 500000000000) = -Real.log (500000000000 / 729105211407) := by
    rw [show ((729105211407 / 500000000000) : ℝ) = ((500000000000 / 729105211407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5066_neg : (42751949 / 250000000) ≤ -Real.log (2000 / 2373) ∧
    -Real.log (2000 / 2373) ≤ (171007797 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 4373)) (n := 12)
    (lo := (42751949 / 250000000)) (hi := (171007797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2373 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2373 / 2000) = 1/(2000 / 2373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5066 : Bounds (42751949 / 250000000) (171007797 / 1000000000) (Real.log (2373 / 2000)) := by
  have h := reflection_log_5066_neg
  have he : Real.log (2373 / 2000) = -Real.log (2000 / 2373) := by
    rw [show ((2373 / 2000) : ℝ) = ((2000 / 2373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5067_neg : (25801169 / 125000000) ≤ -Real.log (1627 / 2000) ∧
    -Real.log (1627 / 2000) ≤ (206409353 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 3627)) (n := 12)
    (lo := (25801169 / 125000000)) (hi := (206409353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1627) = 1/(1627 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5067 : Bounds (-206409353 / 1000000000) (-25801169 / 125000000) (Real.log (1627 / 2000)) := by
  have h := reflection_log_5067_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5068_neg : (93241 / 500000000) ≤ -Real.log (2000000 / 2000373) ∧
    -Real.log (2000000 / 2000373) ≤ (186483 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 4000373)) (n := 12)
    (lo := (93241 / 500000000)) (hi := (186483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000373 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000373 / 2000000) = 1/(2000000 / 2000373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5068 : Bounds (93241 / 500000000) (186483 / 1000000000) (Real.log (2000373 / 2000000)) := by
  have h := reflection_log_5068_neg
  have he : Real.log (2000373 / 2000000) = -Real.log (2000000 / 2000373) := by
    rw [show ((2000373 / 2000000) : ℝ) = ((2000000 / 2000373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5069_neg : (186517 / 1000000000) ≤ -Real.log (1999627 / 2000000) ∧
    -Real.log (1999627 / 2000000) ≤ (93259 / 500000000) := by
  have h := checkLog_sound (w := (373 / 3999627)) (n := 12)
    (lo := (186517 / 1000000000)) (hi := (93259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999627) = 1/(1999627 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5069 : Bounds (-93259 / 500000000) (-186517 / 1000000000) (Real.log (1999627 / 2000000)) := by
  have h := reflection_log_5069_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5070_neg : (895637 / 10000000) ≤ -Real.log (1000000 / 1093697) ∧
    -Real.log (1000000 / 1093697) ≤ (89563701 / 1000000000) := by
  have h := checkLog_sound (w := (93697 / 2093697)) (n := 12)
    (lo := (895637 / 10000000)) (hi := (89563701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093697 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093697 / 1000000) = 1/(1000000 / 1093697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5070 : Bounds (895637 / 10000000) (89563701 / 1000000000) (Real.log (1093697 / 1000000)) := by
  have h := reflection_log_5070_neg
  have he : Real.log (1093697 / 1000000) = -Real.log (1000000 / 1093697) := by
    rw [show ((1093697 / 1000000) : ℝ) = ((1000000 / 1093697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5071_neg : (98381591 / 1000000000) ≤ -Real.log (906303 / 1000000) ∧
    -Real.log (906303 / 1000000) ≤ (12297699 / 125000000) := by
  have h := checkLog_sound (w := (93697 / 1906303)) (n := 12)
    (lo := (98381591 / 1000000000)) (hi := (12297699 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906303) = 1/(906303 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5071 : Bounds (-12297699 / 125000000) (-98381591 / 1000000000) (Real.log (906303 / 1000000)) := by
  have h := reflection_log_5071_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5072_neg : (89780373 / 1000000000) ≤ -Real.log (500000 / 546967) ∧
    -Real.log (500000 / 546967) ≤ (44890187 / 500000000) := by
  have h := checkLog_sound (w := (46967 / 1046967)) (n := 12)
    (lo := (89780373 / 1000000000)) (hi := (44890187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546967 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546967 / 500000) = 1/(500000 / 546967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5072 : Bounds (89780373 / 1000000000) (44890187 / 500000000) (Real.log (546967 / 500000)) := by
  have h := reflection_log_5072_neg
  have he : Real.log (546967 / 500000) = -Real.log (500000 / 546967) := by
    rw [show ((546967 / 500000) : ℝ) = ((500000 / 546967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5073_neg : (98643127 / 1000000000) ≤ -Real.log (453033 / 500000) ∧
    -Real.log (453033 / 500000) ≤ (12330391 / 125000000) := by
  have h := checkLog_sound (w := (46967 / 953033)) (n := 12)
    (lo := (98643127 / 1000000000)) (hi := (12330391 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453033) = 1/(453033 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5073 : Bounds (-12330391 / 125000000) (-98643127 / 1000000000) (Real.log (453033 / 500000)) := by
  have h := reflection_log_5073_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5074_neg : (4431377 / 500000000) ≤ -Real.log (247794100911 / 250000000000) ∧
    -Real.log (247794100911 / 250000000000) ≤ (1772551 / 200000000) := by
  have h := checkLog_sound (w := (2205899089 / 497794100911)) (n := 12)
    (lo := (4431377 / 500000000)) (hi := (1772551 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247794100911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247794100911) = 1/(247794100911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5074 : Bounds (-1772551 / 200000000) (-4431377 / 500000000) (Real.log (247794100911 / 250000000000)) := by
  have h := reflection_log_5074_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5075_neg : (8817891 / 1000000000) ≤ -Real.log (991220872191 / 1000000000000) ∧
    -Real.log (991220872191 / 1000000000000) ≤ (2204473 / 250000000) := by
  have h := checkLog_sound (w := (8779127809 / 1991220872191)) (n := 12)
    (lo := (8817891 / 1000000000)) (hi := (2204473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991220872191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991220872191) = 1/(991220872191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5075 : Bounds (-2204473 / 250000000) (-8817891 / 1000000000) (Real.log (991220872191 / 1000000000000)) := by
  have h := reflection_log_5075_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5076_neg : (46986323 / 250000000) ≤ -Real.log (62500000000 / 75422968367) ∧
    -Real.log (62500000000 / 75422968367) ≤ (187945293 / 1000000000) := by
  have h := checkLog_sound (w := (12922968367 / 137922968367)) (n := 12)
    (lo := (46986323 / 250000000)) (hi := (187945293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75422968367 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75422968367 / 62500000000) = 1/(62500000000 / 75422968367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5076 : Bounds (46986323 / 250000000) (187945293 / 1000000000) (Real.log (75422968367 / 62500000000)) := by
  have h := reflection_log_5076_neg
  have he : Real.log (75422968367 / 62500000000) = -Real.log (62500000000 / 75422968367) := by
    rw [show ((75422968367 / 62500000000) : ℝ) = ((62500000000 / 75422968367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5077_neg : (188423501 / 1000000000) ≤ -Real.log (500000000000 / 603672359409) ∧
    -Real.log (500000000000 / 603672359409) ≤ (94211751 / 500000000) := by
  have h := checkLog_sound (w := (103672359409 / 1103672359409)) (n := 12)
    (lo := (188423501 / 1000000000)) (hi := (94211751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603672359409 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603672359409 / 500000000000) = 1/(500000000000 / 603672359409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5077 : Bounds (188423501 / 1000000000) (94211751 / 500000000) (Real.log (603672359409 / 500000000000)) := by
  have h := reflection_log_5077_neg
  have he : Real.log (603672359409 / 500000000000) = -Real.log (500000000000 / 603672359409) := by
    rw [show ((603672359409 / 500000000000) : ℝ) = ((500000000000 / 603672359409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5078_neg : (188604973 / 500000000) ≤ -Real.log (250000000000 / 364552605703) ∧
    -Real.log (250000000000 / 364552605703) ≤ (377209947 / 1000000000) := by
  have h := checkLog_sound (w := (114552605703 / 614552605703)) (n := 12)
    (lo := (188604973 / 500000000)) (hi := (377209947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364552605703 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364552605703 / 250000000000) = 1/(250000000000 / 364552605703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5078 : Bounds (188604973 / 500000000) (377209947 / 1000000000) (Real.log (364552605703 / 250000000000)) := by
  have h := reflection_log_5078_neg
  have he : Real.log (364552605703 / 250000000000) = -Real.log (250000000000 / 364552605703) := by
    rw [show ((364552605703 / 250000000000) : ℝ) = ((250000000000 / 364552605703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5079_neg : (377417149 / 1000000000) ≤ -Real.log (500000000000 / 729256299939) ∧
    -Real.log (500000000000 / 729256299939) ≤ (7548343 / 20000000) := by
  have h := checkLog_sound (w := (229256299939 / 1229256299939)) (n := 12)
    (lo := (377417149 / 1000000000)) (hi := (7548343 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729256299939 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729256299939 / 500000000000) = 1/(500000000000 / 729256299939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5079 : Bounds (377417149 / 1000000000) (7548343 / 20000000) (Real.log (729256299939 / 500000000000)) := by
  have h := reflection_log_5079_neg
  have he : Real.log (729256299939 / 500000000000) = -Real.log (500000000000 / 729256299939) := by
    rw [show ((729256299939 / 500000000000) : ℝ) = ((500000000000 / 729256299939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5080_neg : (85546037 / 500000000) ≤ -Real.log (5000 / 5933) ∧
    -Real.log (5000 / 5933) ≤ (6843683 / 40000000) := by
  have h := checkLog_sound (w := (933 / 10933)) (n := 12)
    (lo := (85546037 / 500000000)) (hi := (6843683 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5933 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5933 / 5000) = 1/(5000 / 5933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5080 : Bounds (85546037 / 500000000) (6843683 / 40000000) (Real.log (5933 / 5000)) := by
  have h := reflection_log_5080_neg
  have he : Real.log (5933 / 5000) = -Real.log (5000 / 5933) := by
    rw [show ((5933 / 5000) : ℝ) = ((5000 / 5933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5081_neg : (41306457 / 200000000) ≤ -Real.log (4067 / 5000) ∧
    -Real.log (4067 / 5000) ≤ (103266143 / 500000000) := by
  have h := checkLog_sound (w := (933 / 9067)) (n := 12)
    (lo := (41306457 / 200000000)) (hi := (103266143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4067) = 1/(4067 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5081 : Bounds (-103266143 / 500000000) (-41306457 / 200000000) (Real.log (4067 / 5000)) := by
  have h := reflection_log_5081_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5082_neg : (93291 / 500000000) ≤ -Real.log (5000000 / 5000933) ∧
    -Real.log (5000000 / 5000933) ≤ (186583 / 1000000000) := by
  have h := checkLog_sound (w := (933 / 10000933)) (n := 12)
    (lo := (93291 / 500000000)) (hi := (186583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000933 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000933 / 5000000) = 1/(5000000 / 5000933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5082 : Bounds (93291 / 500000000) (186583 / 1000000000) (Real.log (5000933 / 5000000)) := by
  have h := reflection_log_5082_neg
  have he : Real.log (5000933 / 5000000) = -Real.log (5000000 / 5000933) := by
    rw [show ((5000933 / 5000000) : ℝ) = ((5000000 / 5000933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5083_neg : (186617 / 1000000000) ≤ -Real.log (4999067 / 5000000) ∧
    -Real.log (4999067 / 5000000) ≤ (93309 / 500000000) := by
  have h := checkLog_sound (w := (933 / 9999067)) (n := 12)
    (lo := (186617 / 1000000000)) (hi := (93309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999067) = 1/(4999067 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5083 : Bounds (-93309 / 500000000) (-186617 / 1000000000) (Real.log (4999067 / 5000000)) := by
  have h := reflection_log_5083_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5084_neg : (8961033 / 100000000) ≤ -Real.log (250000 / 273437) ∧
    -Real.log (250000 / 273437) ≤ (89610331 / 1000000000) := by
  have h := checkLog_sound (w := (23437 / 523437)) (n := 12)
    (lo := (8961033 / 100000000)) (hi := (89610331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273437 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273437 / 250000) = 1/(250000 / 273437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5084 : Bounds (8961033 / 100000000) (89610331 / 1000000000) (Real.log (273437 / 250000)) := by
  have h := reflection_log_5084_neg
  have he : Real.log (273437 / 250000) = -Real.log (250000 / 273437) := by
    rw [show ((273437 / 250000) : ℝ) = ((250000 / 273437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5085_neg : (19687573 / 200000000) ≤ -Real.log (226563 / 250000) ∧
    -Real.log (226563 / 250000) ≤ (49218933 / 500000000) := by
  have h := checkLog_sound (w := (23437 / 476563)) (n := 12)
    (lo := (19687573 / 200000000)) (hi := (49218933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226563) = 1/(226563 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5085 : Bounds (-49218933 / 500000000) (-19687573 / 200000000) (Real.log (226563 / 250000)) := by
  have h := reflection_log_5085_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5086_neg : (5614187 / 62500000) ≤ -Real.log (200000 / 218797) ∧
    -Real.log (200000 / 218797) ≤ (89826993 / 1000000000) := by
  have h := checkLog_sound (w := (18797 / 418797)) (n := 12)
    (lo := (5614187 / 62500000)) (hi := (89826993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218797 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218797 / 200000) = 1/(200000 / 218797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5086 : Bounds (5614187 / 62500000) (89826993 / 1000000000) (Real.log (218797 / 200000)) := by
  have h := reflection_log_5086_neg
  have he : Real.log (218797 / 200000) = -Real.log (200000 / 218797) := by
    rw [show ((218797 / 200000) : ℝ) = ((200000 / 218797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5087_neg : (12337427 / 125000000) ≤ -Real.log (181203 / 200000) ∧
    -Real.log (181203 / 200000) ≤ (98699417 / 1000000000) := by
  have h := checkLog_sound (w := (18797 / 381203)) (n := 12)
    (lo := (12337427 / 125000000)) (hi := (98699417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181203) = 1/(181203 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5087 : Bounds (-98699417 / 1000000000) (-12337427 / 125000000) (Real.log (181203 / 200000)) := by
  have h := reflection_log_5087_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5088_neg : (1109053 / 125000000) ≤ -Real.log (39646672791 / 40000000000) ∧
    -Real.log (39646672791 / 40000000000) ≤ (354897 / 40000000) := by
  have h := checkLog_sound (w := (353327209 / 79646672791)) (n := 12)
    (lo := (1109053 / 125000000)) (hi := (354897 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39646672791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39646672791) = 1/(39646672791 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5088 : Bounds (-354897 / 40000000) (-1109053 / 125000000) (Real.log (39646672791 / 40000000000)) := by
  have h := reflection_log_5088_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5089_neg : (1765507 / 200000000) ≤ -Real.log (61950707031 / 62500000000) ∧
    -Real.log (61950707031 / 62500000000) ≤ (551721 / 62500000) := by
  have h := checkLog_sound (w := (549292969 / 124450707031)) (n := 12)
    (lo := (1765507 / 200000000)) (hi := (551721 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61950707031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61950707031) = 1/(61950707031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5089 : Bounds (-551721 / 62500000) (-1765507 / 200000000) (Real.log (61950707031 / 62500000000)) := by
  have h := reflection_log_5089_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5090_neg : (47012049 / 250000000) ≤ -Real.log (500000000000 / 603445840671) ∧
    -Real.log (500000000000 / 603445840671) ≤ (188048197 / 1000000000) := by
  have h := checkLog_sound (w := (103445840671 / 1103445840671)) (n := 12)
    (lo := (47012049 / 250000000)) (hi := (188048197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603445840671 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603445840671 / 500000000000) = 1/(500000000000 / 603445840671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5090 : Bounds (47012049 / 250000000) (188048197 / 1000000000) (Real.log (603445840671 / 500000000000)) := by
  have h := reflection_log_5090_neg
  have he : Real.log (603445840671 / 500000000000) = -Real.log (500000000000 / 603445840671) := by
    rw [show ((603445840671 / 500000000000) : ℝ) = ((500000000000 / 603445840671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5091_neg : (188526409 / 1000000000) ≤ -Real.log (500000000000 / 603734485633) ∧
    -Real.log (500000000000 / 603734485633) ≤ (18852641 / 100000000) := by
  have h := checkLog_sound (w := (103734485633 / 1103734485633)) (n := 12)
    (lo := (188526409 / 1000000000)) (hi := (18852641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603734485633 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603734485633 / 500000000000) = 1/(500000000000 / 603734485633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5091 : Bounds (188526409 / 1000000000) (18852641 / 100000000) (Real.log (603734485633 / 500000000000)) := by
  have h := reflection_log_5091_neg
  have he : Real.log (603734485633 / 500000000000) = -Real.log (500000000000 / 603734485633) := by
    rw [show ((603734485633 / 500000000000) : ℝ) = ((500000000000 / 603734485633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5092_neg : (377417149 / 1000000000) ≤ -Real.log (250000000000 / 364628149969) ∧
    -Real.log (250000000000 / 364628149969) ≤ (7548343 / 20000000) := by
  have h := checkLog_sound (w := (114628149969 / 614628149969)) (n := 12)
    (lo := (377417149 / 1000000000)) (hi := (7548343 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364628149969 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364628149969 / 250000000000) = 1/(250000000000 / 364628149969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5092 : Bounds (377417149 / 1000000000) (7548343 / 20000000) (Real.log (364628149969 / 250000000000)) := by
  have h := reflection_log_5092_neg
  have he : Real.log (364628149969 / 250000000000) = -Real.log (250000000000 / 364628149969) := by
    rw [show ((364628149969 / 250000000000) : ℝ) = ((250000000000 / 364628149969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5093_neg : (9440609 / 25000000) ≤ -Real.log (500000000000 / 729407425621) ∧
    -Real.log (500000000000 / 729407425621) ≤ (377624361 / 1000000000) := by
  have h := checkLog_sound (w := (229407425621 / 1229407425621)) (n := 12)
    (lo := (9440609 / 25000000)) (hi := (377624361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729407425621 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729407425621 / 500000000000) = 1/(500000000000 / 729407425621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5093 : Bounds (9440609 / 25000000) (377624361 / 1000000000) (Real.log (729407425621 / 500000000000)) := by
  have h := reflection_log_5093_neg
  have he : Real.log (729407425621 / 500000000000) = -Real.log (500000000000 / 729407425621) := by
    rw [show ((729407425621 / 500000000000) : ℝ) = ((500000000000 / 729407425621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5094_neg : (34235269 / 200000000) ≤ -Real.log (10000 / 11867) ∧
    -Real.log (10000 / 11867) ≤ (85588173 / 500000000) := by
  have h := checkLog_sound (w := (1867 / 21867)) (n := 12)
    (lo := (34235269 / 200000000)) (hi := (85588173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11867 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11867 / 10000) = 1/(10000 / 11867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5094 : Bounds (34235269 / 200000000) (85588173 / 500000000) (Real.log (11867 / 10000)) := by
  have h := reflection_log_5094_neg
  have he : Real.log (11867 / 10000) = -Real.log (10000 / 11867) := by
    rw [show ((11867 / 10000) : ℝ) = ((10000 / 11867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5095_neg : (206655233 / 1000000000) ≤ -Real.log (8133 / 10000) ∧
    -Real.log (8133 / 10000) ≤ (103327617 / 500000000) := by
  have h := checkLog_sound (w := (1867 / 18133)) (n := 12)
    (lo := (206655233 / 1000000000)) (hi := (103327617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8133) = 1/(8133 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5095 : Bounds (-103327617 / 500000000) (-206655233 / 1000000000) (Real.log (8133 / 10000)) := by
  have h := reflection_log_5095_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5096_neg : (93341 / 500000000) ≤ -Real.log (10000000 / 10001867) ∧
    -Real.log (10000000 / 10001867) ≤ (186683 / 1000000000) := by
  have h := checkLog_sound (w := (1867 / 20001867)) (n := 12)
    (lo := (93341 / 500000000)) (hi := (186683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001867 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001867 / 10000000) = 1/(10000000 / 10001867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5096 : Bounds (93341 / 500000000) (186683 / 1000000000) (Real.log (10001867 / 10000000)) := by
  have h := reflection_log_5096_neg
  have he : Real.log (10001867 / 10000000) = -Real.log (10000000 / 10001867) := by
    rw [show ((10001867 / 10000000) : ℝ) = ((10000000 / 10001867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5097_neg : (186717 / 1000000000) ≤ -Real.log (9998133 / 10000000) ∧
    -Real.log (9998133 / 10000000) ≤ (93359 / 500000000) := by
  have h := checkLog_sound (w := (1867 / 19998133)) (n := 12)
    (lo := (186717 / 1000000000)) (hi := (93359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998133) = 1/(9998133 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5097 : Bounds (-93359 / 500000000) (-186717 / 1000000000) (Real.log (9998133 / 10000000)) := by
  have h := reflection_log_5097_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5098_neg : (89656957 / 1000000000) ≤ -Real.log (1000000 / 1093799) ∧
    -Real.log (1000000 / 1093799) ≤ (44828479 / 500000000) := by
  have h := checkLog_sound (w := (93799 / 2093799)) (n := 12)
    (lo := (89656957 / 1000000000)) (hi := (44828479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093799 / 1000000) = 1/(1000000 / 1093799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5098 : Bounds (89656957 / 1000000000) (44828479 / 500000000) (Real.log (1093799 / 1000000)) := by
  have h := reflection_log_5098_neg
  have he : Real.log (1093799 / 1000000) = -Real.log (1000000 / 1093799) := by
    rw [show ((1093799 / 1000000) : ℝ) = ((1000000 / 1093799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5099_neg : (98494143 / 1000000000) ≤ -Real.log (906201 / 1000000) ∧
    -Real.log (906201 / 1000000) ≤ (1538971 / 15625000) := by
  have h := checkLog_sound (w := (93799 / 1906201)) (n := 12)
    (lo := (98494143 / 1000000000)) (hi := (1538971 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906201) = 1/(906201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5099 : Bounds (-1538971 / 15625000) (-98494143 / 1000000000) (Real.log (906201 / 1000000)) := by
  have h := reflection_log_5099_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5100_neg : (8987361 / 100000000) ≤ -Real.log (250000 / 273509) ∧
    -Real.log (250000 / 273509) ≤ (89873611 / 1000000000) := by
  have h := checkLog_sound (w := (23509 / 523509)) (n := 12)
    (lo := (8987361 / 100000000)) (hi := (89873611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273509 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273509 / 250000) = 1/(250000 / 273509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5100 : Bounds (8987361 / 100000000) (89873611 / 1000000000) (Real.log (273509 / 250000)) := by
  have h := reflection_log_5100_neg
  have he : Real.log (273509 / 250000) = -Real.log (250000 / 273509) := by
    rw [show ((273509 / 250000) : ℝ) = ((250000 / 273509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5101_neg : (24688927 / 250000000) ≤ -Real.log (226491 / 250000) ∧
    -Real.log (226491 / 250000) ≤ (98755709 / 1000000000) := by
  have h := checkLog_sound (w := (23509 / 476491)) (n := 12)
    (lo := (24688927 / 250000000)) (hi := (98755709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226491) = 1/(226491 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5101 : Bounds (-98755709 / 1000000000) (-24688927 / 250000000) (Real.log (226491 / 250000)) := by
  have h := reflection_log_5101_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5102_neg : (4441049 / 500000000) ≤ -Real.log (61947326919 / 62500000000) ∧
    -Real.log (61947326919 / 62500000000) ≤ (8882099 / 1000000000) := by
  have h := checkLog_sound (w := (552673081 / 124447326919)) (n := 12)
    (lo := (4441049 / 500000000)) (hi := (8882099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61947326919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61947326919) = 1/(61947326919 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5102 : Bounds (-8882099 / 1000000000) (-4441049 / 500000000) (Real.log (61947326919 / 62500000000)) := by
  have h := reflection_log_5102_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5103_neg : (1767437 / 200000000) ≤ -Real.log (991201747599 / 1000000000000) ∧
    -Real.log (991201747599 / 1000000000000) ≤ (4418593 / 500000000) := by
  have h := checkLog_sound (w := (8798252401 / 1991201747599)) (n := 12)
    (lo := (1767437 / 200000000)) (hi := (4418593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991201747599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991201747599) = 1/(991201747599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5103 : Bounds (-4418593 / 500000000) (-1767437 / 200000000) (Real.log (991201747599 / 1000000000000)) := by
  have h := reflection_log_5103_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5104_neg : (1881511 / 10000000) ≤ -Real.log (250000000000 / 301753970697) ∧
    -Real.log (250000000000 / 301753970697) ≤ (188151101 / 1000000000) := by
  have h := checkLog_sound (w := (51753970697 / 551753970697)) (n := 12)
    (lo := (1881511 / 10000000)) (hi := (188151101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301753970697 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301753970697 / 250000000000) = 1/(250000000000 / 301753970697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5104 : Bounds (1881511 / 10000000) (188151101 / 1000000000) (Real.log (301753970697 / 250000000000)) := by
  have h := reflection_log_5104_neg
  have he : Real.log (301753970697 / 250000000000) = -Real.log (250000000000 / 301753970697) := by
    rw [show ((301753970697 / 250000000000) : ℝ) = ((250000000000 / 301753970697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5105_neg : (188629319 / 1000000000) ≤ -Real.log (500000000000 / 603796618851) ∧
    -Real.log (500000000000 / 603796618851) ≤ (4715733 / 25000000) := by
  have h := checkLog_sound (w := (103796618851 / 1103796618851)) (n := 12)
    (lo := (188629319 / 1000000000)) (hi := (4715733 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603796618851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603796618851 / 500000000000) = 1/(500000000000 / 603796618851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5105 : Bounds (188629319 / 1000000000) (4715733 / 25000000) (Real.log (603796618851 / 500000000000)) := by
  have h := reflection_log_5105_neg
  have he : Real.log (603796618851 / 500000000000) = -Real.log (500000000000 / 603796618851) := by
    rw [show ((603796618851 / 500000000000) : ℝ) = ((500000000000 / 603796618851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5106_neg : (9440609 / 25000000) ≤ -Real.log (25000000000 / 36470371281) ∧
    -Real.log (25000000000 / 36470371281) ≤ (377624361 / 1000000000) := by
  have h := checkLog_sound (w := (11470371281 / 61470371281)) (n := 12)
    (lo := (9440609 / 25000000)) (hi := (377624361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36470371281 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36470371281 / 25000000000) = 1/(25000000000 / 36470371281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5106 : Bounds (9440609 / 25000000) (377624361 / 1000000000) (Real.log (36470371281 / 25000000000)) := by
  have h := reflection_log_5106_neg
  have he : Real.log (36470371281 / 25000000000) = -Real.log (25000000000 / 36470371281) := by
    rw [show ((36470371281 / 25000000000) : ℝ) = ((25000000000 / 36470371281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5107_neg : (377831579 / 1000000000) ≤ -Real.log (500000000000 / 729558588467) ∧
    -Real.log (500000000000 / 729558588467) ≤ (18891579 / 50000000) := by
  have h := checkLog_sound (w := (229558588467 / 1229558588467)) (n := 12)
    (lo := (377831579 / 1000000000)) (hi := (18891579 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729558588467 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729558588467 / 500000000000) = 1/(500000000000 / 729558588467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5107 : Bounds (377831579 / 1000000000) (18891579 / 50000000) (Real.log (729558588467 / 500000000000)) := by
  have h := reflection_log_5107_neg
  have he : Real.log (729558588467 / 500000000000) = -Real.log (500000000000 / 729558588467) := by
    rw [show ((729558588467 / 500000000000) : ℝ) = ((500000000000 / 729558588467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5108_neg : (171260609 / 1000000000) ≤ -Real.log (2500 / 2967) ∧
    -Real.log (2500 / 2967) ≤ (17126061 / 100000000) := by
  have h := checkLog_sound (w := (467 / 5467)) (n := 12)
    (lo := (171260609 / 1000000000)) (hi := (17126061 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2967 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2967 / 2500) = 1/(2500 / 2967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5108 : Bounds (171260609 / 1000000000) (17126061 / 100000000) (Real.log (2967 / 2500)) := by
  have h := reflection_log_5108_neg
  have he : Real.log (2967 / 2500) = -Real.log (2500 / 2967) := by
    rw [show ((2967 / 2500) : ℝ) = ((2500 / 2967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5109_neg : (206778197 / 1000000000) ≤ -Real.log (2033 / 2500) ∧
    -Real.log (2033 / 2500) ≤ (103389099 / 500000000) := by
  have h := checkLog_sound (w := (467 / 4533)) (n := 12)
    (lo := (206778197 / 1000000000)) (hi := (103389099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2033) = 1/(2033 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5109 : Bounds (-103389099 / 500000000) (-206778197 / 1000000000) (Real.log (2033 / 2500)) := by
  have h := reflection_log_5109_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5110_neg : (93391 / 500000000) ≤ -Real.log (2500000 / 2500467) ∧
    -Real.log (2500000 / 2500467) ≤ (186783 / 1000000000) := by
  have h := checkLog_sound (w := (467 / 5000467)) (n := 12)
    (lo := (93391 / 500000000)) (hi := (186783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500467 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500467 / 2500000) = 1/(2500000 / 2500467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5110 : Bounds (93391 / 500000000) (186783 / 1000000000) (Real.log (2500467 / 2500000)) := by
  have h := reflection_log_5110_neg
  have he : Real.log (2500467 / 2500000) = -Real.log (2500000 / 2500467) := by
    rw [show ((2500467 / 2500000) : ℝ) = ((2500000 / 2500467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5111_neg : (186817 / 1000000000) ≤ -Real.log (2499533 / 2500000) ∧
    -Real.log (2499533 / 2500000) ≤ (93409 / 500000000) := by
  have h := checkLog_sound (w := (467 / 4999533)) (n := 12)
    (lo := (186817 / 1000000000)) (hi := (93409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499533) = 1/(2499533 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5111 : Bounds (-93409 / 500000000) (-186817 / 1000000000) (Real.log (2499533 / 2500000)) := by
  have h := reflection_log_5111_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5112_neg : (89703583 / 1000000000) ≤ -Real.log (20000 / 21877) ∧
    -Real.log (20000 / 21877) ≤ (2803237 / 31250000) := by
  have h := checkLog_sound (w := (1877 / 41877)) (n := 12)
    (lo := (89703583 / 1000000000)) (hi := (2803237 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21877 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21877 / 20000) = 1/(20000 / 21877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5112 : Bounds (89703583 / 1000000000) (2803237 / 31250000) (Real.log (21877 / 20000)) := by
  have h := reflection_log_5112_neg
  have he : Real.log (21877 / 20000) = -Real.log (20000 / 21877) := by
    rw [show ((21877 / 20000) : ℝ) = ((20000 / 21877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5113_neg : (98550423 / 1000000000) ≤ -Real.log (18123 / 20000) ∧
    -Real.log (18123 / 20000) ≤ (12318803 / 125000000) := by
  have h := checkLog_sound (w := (1877 / 38123)) (n := 12)
    (lo := (98550423 / 1000000000)) (hi := (12318803 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18123) = 1/(18123 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5113 : Bounds (-12318803 / 125000000) (-98550423 / 1000000000) (Real.log (18123 / 20000)) := by
  have h := reflection_log_5113_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5114_neg : (3596809 / 40000000) ≤ -Real.log (1000000 / 1094087) ∧
    -Real.log (1000000 / 1094087) ≤ (44960113 / 500000000) := by
  have h := checkLog_sound (w := (94087 / 2094087)) (n := 12)
    (lo := (3596809 / 40000000)) (hi := (44960113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094087 / 1000000) = 1/(1000000 / 1094087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5114 : Bounds (3596809 / 40000000) (44960113 / 500000000) (Real.log (1094087 / 1000000)) := by
  have h := reflection_log_5114_neg
  have he : Real.log (1094087 / 1000000) = -Real.log (1000000 / 1094087) := by
    rw [show ((1094087 / 1000000) : ℝ) = ((1000000 / 1094087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5115_neg : (24703001 / 250000000) ≤ -Real.log (905913 / 1000000) ∧
    -Real.log (905913 / 1000000) ≤ (19762401 / 200000000) := by
  have h := checkLog_sound (w := (94087 / 1905913)) (n := 12)
    (lo := (24703001 / 250000000)) (hi := (19762401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905913) = 1/(905913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5115 : Bounds (-19762401 / 200000000) (-24703001 / 250000000) (Real.log (905913 / 1000000)) := by
  have h := reflection_log_5115_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5116_neg : (4445889 / 500000000) ≤ -Real.log (991147636431 / 1000000000000) ∧
    -Real.log (991147636431 / 1000000000000) ≤ (8891779 / 1000000000) := by
  have h := checkLog_sound (w := (8852363569 / 1991147636431)) (n := 12)
    (lo := (4445889 / 500000000)) (hi := (8891779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991147636431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991147636431) = 1/(991147636431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5116 : Bounds (-8891779 / 1000000000) (-4445889 / 500000000) (Real.log (991147636431 / 1000000000000)) := by
  have h := reflection_log_5116_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5117_neg : (221171 / 25000000) ≤ -Real.log (396476871 / 400000000) ∧
    -Real.log (396476871 / 400000000) ≤ (8846841 / 1000000000) := by
  have h := checkLog_sound (w := (3523129 / 796476871)) (n := 12)
    (lo := (221171 / 25000000)) (hi := (8846841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 396476871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 396476871) = 1/(396476871 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5117 : Bounds (-8846841 / 1000000000) (-221171 / 25000000) (Real.log (396476871 / 400000000)) := by
  have h := reflection_log_5117_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5118_neg : (94127003 / 500000000) ≤ -Real.log (125000000000 / 150892512277) ∧
    -Real.log (125000000000 / 150892512277) ≤ (188254007 / 1000000000) := by
  have h := checkLog_sound (w := (25892512277 / 275892512277)) (n := 12)
    (lo := (94127003 / 500000000)) (hi := (188254007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150892512277 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150892512277 / 125000000000) = 1/(125000000000 / 150892512277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5118 : Bounds (94127003 / 500000000) (188254007 / 1000000000) (Real.log (150892512277 / 125000000000)) := by
  have h := reflection_log_5118_neg
  have he : Real.log (150892512277 / 125000000000) = -Real.log (125000000000 / 150892512277) := by
    rw [show ((150892512277 / 125000000000) : ℝ) = ((125000000000 / 150892512277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5119_neg : (188732229 / 1000000000) ≤ -Real.log (100000000000 / 120771751813) ∧
    -Real.log (100000000000 / 120771751813) ≤ (18873223 / 100000000) := by
  have h := checkLog_sound (w := (20771751813 / 220771751813)) (n := 12)
    (lo := (188732229 / 1000000000)) (hi := (18873223 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120771751813 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120771751813 / 100000000000) = 1/(100000000000 / 120771751813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5119 : Bounds (188732229 / 1000000000) (18873223 / 100000000) (Real.log (120771751813 / 100000000000)) := by
  have h := reflection_log_5119_neg
  have he : Real.log (120771751813 / 100000000000) = -Real.log (100000000000 / 120771751813) := by
    rw [show ((120771751813 / 100000000000) : ℝ) = ((100000000000 / 120771751813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
