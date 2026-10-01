import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14976_neg : (1446745123 / 1000000000) ≤ -Real.log (100000000000 / 424926116649) ∧
    -Real.log (100000000000 / 424926116649) ≤ (723372563 / 500000000) := by
  have h := checkLog_sound (w := (24926116649 / 824926116649)) (n := 12)
    (lo := (60450763 / 1000000000)) (hi := (15112691 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((424926116649 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(424926116649 / 400000000000) = 1/(100000000000 / 424926116649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14976 : Bounds (1446745123 / 1000000000) (723372563 / 500000000) (Real.log (424926116649 / 100000000000)) := by
  have h := reflection_log_14976_neg
  have he : Real.log (424926116649 / 100000000000) = -Real.log (100000000000 / 424926116649) := by
    rw [show ((424926116649 / 100000000000) : ℝ) = ((100000000000 / 424926116649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14977_neg : (1452871711 / 1000000000) ≤ -Real.log (500000000000 / 2137687275797) ∧
    -Real.log (500000000000 / 2137687275797) ≤ (726435857 / 500000000) := by
  have h := checkLog_sound (w := (137687275797 / 4137687275797)) (n := 12)
    (lo := (66577351 / 1000000000)) (hi := (8322169 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2137687275797 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2137687275797 / 2000000000000) = 1/(500000000000 / 2137687275797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14977 : Bounds (1452871711 / 1000000000) (726435857 / 500000000) (Real.log (2137687275797 / 500000000000)) := by
  have h := reflection_log_14977_neg
  have he : Real.log (2137687275797 / 500000000000) = -Real.log (500000000000 / 2137687275797) := by
    rw [show ((2137687275797 / 500000000000) : ℝ) = ((500000000000 / 2137687275797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14978_neg : (1072868409 / 250000000) ≤ -Real.log (500000000000 / 36537037037037) ∧
    -Real.log (500000000000 / 36537037037037) ≤ (4291473643 / 1000000000) := by
  have h := checkLog_sound (w := (4537037037037 / 68537037037037)) (n := 12)
    (lo := (33147639 / 250000000)) (hi := (132590557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36537037037037 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(36537037037037 / 32000000000000) = 1/(500000000000 / 36537037037037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14978 : Bounds (1072868409 / 250000000) (4291473643 / 1000000000) (Real.log (36537037037037 / 500000000000)) := by
  have h := reflection_log_14978_neg
  have he : Real.log (36537037037037 / 500000000000) = -Real.log (500000000000 / 36537037037037) := by
    rw [show ((36537037037037 / 500000000000) : ℝ) = ((500000000000 / 36537037037037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14979_neg : (2164860339 / 500000000) ≤ -Real.log (500000000000 / 37961538461539) ∧
    -Real.log (500000000000 / 37961538461539) ≤ (865944137 / 200000000) := by
  have h := checkLog_sound (w := (5961538461539 / 69961538461539)) (n := 12)
    (lo := (85418799 / 500000000)) (hi := (170837599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37961538461539 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(37961538461539 / 32000000000000) = 1/(500000000000 / 37961538461539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14979 : Bounds (2164860339 / 500000000) (865944137 / 200000000) (Real.log (37961538461539 / 500000000000)) := by
  have h := reflection_log_14979_neg
  have he : Real.log (37961538461539 / 500000000000) = -Real.log (500000000000 / 37961538461539) := by
    rw [show ((37961538461539 / 500000000000) : ℝ) = ((500000000000 / 37961538461539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14980_neg : (340284199 / 500000000) ≤ -Real.log (40 / 79) ∧
    -Real.log (40 / 79) ≤ (680568399 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 119)) (n := 12)
    (lo := (340284199 / 500000000)) (hi := (680568399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79 / 40) = 1/(40 / 79) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14980 : Bounds (340284199 / 500000000) (680568399 / 1000000000) (Real.log (79 / 40)) := by
  have h := reflection_log_14980_neg
  have he : Real.log (79 / 40) = -Real.log (40 / 79) := by
    rw [show ((79 / 40) : ℝ) = ((40 / 79) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14981_neg : (3688879451 / 1000000000) ≤ -Real.log (1 / 40) ∧
    -Real.log (1 / 40) ≤ (3688879457 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5 / 4) = 1/(1 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14981 : Bounds (-3688879457 / 1000000000) (-3688879451 / 1000000000) (Real.log (1 / 40)) := by
  have h := reflection_log_14981_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14982_neg : (243631 / 250000000) ≤ -Real.log (40000 / 40039) ∧
    -Real.log (40000 / 40039) ≤ (38981 / 40000000) := by
  have h := checkLog_sound (w := (39 / 80039)) (n := 12)
    (lo := (243631 / 250000000)) (hi := (38981 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40039 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40039 / 40000) = 1/(40000 / 40039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14982 : Bounds (243631 / 250000000) (38981 / 40000000) (Real.log (40039 / 40000)) := by
  have h := reflection_log_14982_neg
  have he : Real.log (40039 / 40000) = -Real.log (40000 / 40039) := by
    rw [show ((40039 / 40000) : ℝ) = ((40000 / 40039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14983_neg : (39019 / 40000000) ≤ -Real.log (39961 / 40000) ∧
    -Real.log (39961 / 40000) ≤ (243869 / 250000000) := by
  have h := checkLog_sound (w := (39 / 79961)) (n := 12)
    (lo := (39019 / 40000000)) (hi := (243869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 39961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 39961) = 1/(39961 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14983 : Bounds (-243869 / 250000000) (-39019 / 40000000) (Real.log (39961 / 40000)) := by
  have h := reflection_log_14983_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14984_neg : (301607 / 625000) ≤ -Real.log (200000 / 324047) ∧
    -Real.log (200000 / 324047) ≤ (482571201 / 1000000000) := by
  have h := checkLog_sound (w := (124047 / 524047)) (n := 12)
    (lo := (301607 / 625000)) (hi := (482571201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324047 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(324047 / 200000) = 1/(200000 / 324047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14984 : Bounds (301607 / 625000) (482571201 / 1000000000) (Real.log (324047 / 200000)) := by
  have h := reflection_log_14984_neg
  have he : Real.log (324047 / 200000) = -Real.log (200000 / 324047) := by
    rw [show ((324047 / 200000) : ℝ) = ((200000 / 324047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14985_neg : (484101319 / 500000000) ≤ -Real.log (75953 / 200000) ∧
    -Real.log (75953 / 200000) ≤ (12102533 / 12500000) := by
  have h := checkLog_sound (w := (24047 / 175953)) (n := 12)
    (lo := (137527729 / 500000000)) (hi := (275055459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 75953) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 75953) = 1/(75953 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14985 : Bounds (-12102533 / 12500000) (-484101319 / 500000000) (Real.log (75953 / 200000)) := by
  have h := reflection_log_14985_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14986_neg : (483739483 / 1000000000) ≤ -Real.log (1000000 / 1622129) ∧
    -Real.log (1000000 / 1622129) ≤ (120934871 / 250000000) := by
  have h := checkLog_sound (w := (622129 / 2622129)) (n := 12)
    (lo := (483739483 / 1000000000)) (hi := (120934871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1622129 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1622129 / 1000000) = 1/(1000000 / 1622129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14986 : Bounds (483739483 / 1000000000) (120934871 / 250000000) (Real.log (1622129 / 1000000)) := by
  have h := reflection_log_14986_neg
  have he : Real.log (1622129 / 1000000) = -Real.log (1000000 / 1622129) := by
    rw [show ((1622129 / 1000000) : ℝ) = ((1000000 / 1622129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14987_neg : (97320241 / 100000000) ≤ -Real.log (377871 / 1000000) ∧
    -Real.log (377871 / 1000000) ≤ (243300603 / 250000000) := by
  have h := checkLog_sound (w := (122129 / 877871)) (n := 12)
    (lo := (28005523 / 100000000)) (hi := (280055231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 377871) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 377871) = 1/(377871 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14987 : Bounds (-243300603 / 250000000) (-97320241 / 100000000) (Real.log (377871 / 1000000)) := by
  have h := reflection_log_14987_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14988_neg : (489462927 / 1000000000) ≤ -Real.log (612955507359 / 1000000000000) ∧
    -Real.log (612955507359 / 1000000000000) ≤ (30591433 / 62500000) := by
  have h := checkLog_sound (w := (387044492641 / 1612955507359)) (n := 12)
    (lo := (489462927 / 1000000000)) (hi := (30591433 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 612955507359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 612955507359) = 1/(612955507359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14988 : Bounds (-30591433 / 62500000) (-489462927 / 1000000000) (Real.log (612955507359 / 1000000000000)) := by
  have h := reflection_log_14988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14989_neg : (242815719 / 500000000) ≤ -Real.log (24612341791 / 40000000000) ∧
    -Real.log (24612341791 / 40000000000) ≤ (485631439 / 1000000000) := by
  have h := checkLog_sound (w := (15387658209 / 64612341791)) (n := 12)
    (lo := (242815719 / 500000000)) (hi := (485631439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 24612341791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 24612341791) = 1/(24612341791 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14989 : Bounds (-485631439 / 1000000000) (-242815719 / 500000000) (Real.log (24612341791 / 40000000000)) := by
  have h := reflection_log_14989_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14990_neg : (1450773837 / 1000000000) ≤ -Real.log (500000000000 / 2133207378247) ∧
    -Real.log (500000000000 / 2133207378247) ≤ (18134673 / 12500000) := by
  have h := checkLog_sound (w := (133207378247 / 4133207378247)) (n := 12)
    (lo := (64479477 / 1000000000)) (hi := (32239739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2133207378247 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2133207378247 / 2000000000000) = 1/(500000000000 / 2133207378247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14990 : Bounds (1450773837 / 1000000000) (18134673 / 12500000) (Real.log (2133207378247 / 500000000000)) := by
  have h := reflection_log_14990_neg
  have he : Real.log (2133207378247 / 500000000000) = -Real.log (500000000000 / 2133207378247) := by
    rw [show ((2133207378247 / 500000000000) : ℝ) = ((500000000000 / 2133207378247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14991_neg : (728470947 / 500000000) ≤ -Real.log (100000000000 / 429281156797) ∧
    -Real.log (100000000000 / 429281156797) ≤ (1456941897 / 1000000000) := by
  have h := checkLog_sound (w := (29281156797 / 829281156797)) (n := 12)
    (lo := (35323767 / 500000000)) (hi := (14129507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429281156797 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(429281156797 / 400000000000) = 1/(100000000000 / 429281156797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14991 : Bounds (728470947 / 500000000) (1456941897 / 1000000000) (Real.log (429281156797 / 100000000000)) := by
  have h := reflection_log_14991_neg
  have he : Real.log (429281156797 / 100000000000) = -Real.log (100000000000 / 429281156797) := by
    rw [show ((429281156797 / 100000000000) : ℝ) = ((100000000000 / 429281156797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14992_neg : (2164860339 / 500000000) ≤ -Real.log (250000000000 / 18980769230769) ∧
    -Real.log (250000000000 / 18980769230769) ≤ (865944137 / 200000000) := by
  have h := checkLog_sound (w := (2980769230769 / 34980769230769)) (n := 12)
    (lo := (85418799 / 500000000)) (hi := (170837599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18980769230769 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18980769230769 / 16000000000000) = 1/(250000000000 / 18980769230769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14992 : Bounds (2164860339 / 500000000) (865944137 / 200000000) (Real.log (18980769230769 / 250000000000)) := by
  have h := reflection_log_14992_neg
  have he : Real.log (18980769230769 / 250000000000) = -Real.log (250000000000 / 18980769230769) := by
    rw [show ((18980769230769 / 250000000000) : ℝ) = ((250000000000 / 18980769230769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14993_neg : (4369447849 / 1000000000) ≤ -Real.log (1 / 79) ∧
    -Real.log (1 / 79) ≤ (273090491 / 62500000) := by
  have h := checkLog_sound (w := (15 / 143)) (n := 12)
    (lo := (210564769 / 1000000000)) (hi := (21056477 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79 / 64) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(79 / 64) = 1/(1 / 79) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14993 : Bounds (4369447849 / 1000000000) (273090491 / 62500000) (Real.log (79 / 1)) := by
  have h := reflection_log_14993_neg
  have he : Real.log (79 / 1) = -Real.log (1 / 79) := by
    rw [show ((79 / 1) : ℝ) = ((1 / 79) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14994_neg : (681074599 / 1000000000) ≤ -Real.log (125 / 247) ∧
    -Real.log (125 / 247) ≤ (3405373 / 5000000) := by
  have h := checkLog_sound (w := (61 / 186)) (n := 12)
    (lo := (681074599 / 1000000000)) (hi := (3405373 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247 / 125) = 1/(125 / 247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14994 : Bounds (681074599 / 1000000000) (3405373 / 5000000) (Real.log (247 / 125)) := by
  have h := reflection_log_14994_neg
  have he : Real.log (247 / 125) = -Real.log (125 / 247) := by
    rw [show ((247 / 125) : ℝ) = ((125 / 247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14995_neg : (745940289 / 200000000) ≤ -Real.log (3 / 125) ∧
    -Real.log (3 / 125) ≤ (3729701451 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 221)) (n := 12)
    (lo := (52793109 / 200000000)) (hi := (131982773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 96) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 96) = 1/(3 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14995 : Bounds (-3729701451 / 1000000000) (-745940289 / 200000000) (Real.log (3 / 125)) := by
  have h := reflection_log_14995_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14996_neg : (243881 / 250000000) ≤ -Real.log (62500 / 62561) ∧
    -Real.log (62500 / 62561) ≤ (39021 / 40000000) := by
  have h := checkLog_sound (w := (61 / 125061)) (n := 12)
    (lo := (243881 / 250000000)) (hi := (39021 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62561 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62561 / 62500) = 1/(62500 / 62561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14996 : Bounds (243881 / 250000000) (39021 / 40000000) (Real.log (62561 / 62500)) := by
  have h := reflection_log_14996_neg
  have he : Real.log (62561 / 62500) = -Real.log (62500 / 62561) := by
    rw [show ((62561 / 62500) : ℝ) = ((62500 / 62561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14997_neg : (244119 / 250000000) ≤ -Real.log (62439 / 62500) ∧
    -Real.log (62439 / 62500) ≤ (976477 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 124939)) (n := 12)
    (lo := (244119 / 250000000)) (hi := (976477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62439) = 1/(62439 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14997 : Bounds (-976477 / 1000000000) (-244119 / 250000000) (Real.log (62439 / 62500)) := by
  have h := reflection_log_14997_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14998_neg : (120835599 / 250000000) ≤ -Real.log (200000 / 324297) ∧
    -Real.log (200000 / 324297) ≤ (483342397 / 1000000000) := by
  have h := checkLog_sound (w := (124297 / 524297)) (n := 12)
    (lo := (120835599 / 250000000)) (hi := (483342397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324297 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(324297 / 200000) = 1/(200000 / 324297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14998 : Bounds (120835599 / 250000000) (483342397 / 1000000000) (Real.log (324297 / 200000)) := by
  have h := reflection_log_14998_neg
  have he : Real.log (324297 / 200000) = -Real.log (200000 / 324297) := by
    rw [show ((324297 / 200000) : ℝ) = ((200000 / 324297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14999_neg : (121437447 / 125000000) ≤ -Real.log (75703 / 200000) ∧
    -Real.log (75703 / 200000) ≤ (485749789 / 500000000) := by
  have h := checkLog_sound (w := (24297 / 175703)) (n := 12)
    (lo := (69588099 / 250000000)) (hi := (278352397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 75703) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 75703) = 1/(75703 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14999 : Bounds (-485749789 / 500000000) (-121437447 / 125000000) (Real.log (75703 / 200000)) := by
  have h := reflection_log_14999_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15000_neg : (484515323 / 1000000000) ≤ -Real.log (250000 / 405847) ∧
    -Real.log (250000 / 405847) ≤ (121128831 / 250000000) := by
  have h := checkLog_sound (w := (155847 / 655847)) (n := 12)
    (lo := (484515323 / 1000000000)) (hi := (121128831 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((405847 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(405847 / 250000) = 1/(250000 / 405847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15000 : Bounds (484515323 / 1000000000) (121128831 / 250000000) (Real.log (405847 / 250000)) := by
  have h := reflection_log_15000_neg
  have he : Real.log (405847 / 250000) = -Real.log (250000 / 405847) := by
    rw [show ((405847 / 250000) : ℝ) = ((250000 / 405847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15001_neg : (488269899 / 500000000) ≤ -Real.log (94153 / 250000) ∧
    -Real.log (94153 / 250000) ≤ (4882699 / 5000000) := by
  have h := checkLog_sound (w := (30847 / 219153)) (n := 12)
    (lo := (141696309 / 500000000)) (hi := (283392619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94153) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 94153) = 1/(94153 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15001 : Bounds (-4882699 / 5000000) (-488269899 / 500000000) (Real.log (94153 / 250000)) := by
  have h := reflection_log_15001_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15002_neg : (19680979 / 40000000) ≤ -Real.log (38211712591 / 62500000000) ∧
    -Real.log (38211712591 / 62500000000) ≤ (123006119 / 250000000) := by
  have h := checkLog_sound (w := (24288287409 / 100711712591)) (n := 12)
    (lo := (19680979 / 40000000)) (hi := (123006119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 38211712591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 38211712591) = 1/(38211712591 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15002 : Bounds (-123006119 / 250000000) (-19680979 / 40000000) (Real.log (38211712591 / 62500000000)) := by
  have h := reflection_log_15002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15003_neg : (24407859 / 50000000) ≤ -Real.log (24550255791 / 40000000000) ∧
    -Real.log (24550255791 / 40000000000) ≤ (488157181 / 1000000000) := by
  have h := checkLog_sound (w := (15449744209 / 64550255791)) (n := 12)
    (lo := (24407859 / 50000000)) (hi := (488157181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 24550255791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 24550255791) = 1/(24550255791 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15003 : Bounds (-488157181 / 1000000000) (-24407859 / 50000000) (Real.log (24550255791 / 40000000000)) := by
  have h := reflection_log_15003_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15004_neg : (1454841971 / 1000000000) ≤ -Real.log (125000000000 / 535475806771) ∧
    -Real.log (125000000000 / 535475806771) ≤ (727420987 / 500000000) := by
  have h := checkLog_sound (w := (35475806771 / 1035475806771)) (n := 12)
    (lo := (68547611 / 1000000000)) (hi := (17136903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((535475806771 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(535475806771 / 500000000000) = 1/(125000000000 / 535475806771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15004 : Bounds (1454841971 / 1000000000) (727420987 / 500000000) (Real.log (535475806771 / 125000000000)) := by
  have h := reflection_log_15004_neg
  have he : Real.log (535475806771 / 125000000000) = -Real.log (125000000000 / 535475806771) := by
    rw [show ((535475806771 / 125000000000) : ℝ) = ((125000000000 / 535475806771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15005_neg : (1461055121 / 1000000000) ≤ -Real.log (100000000000 / 431050524147) ∧
    -Real.log (100000000000 / 431050524147) ≤ (365263781 / 250000000) := by
  have h := checkLog_sound (w := (31050524147 / 831050524147)) (n := 12)
    (lo := (74760761 / 1000000000)) (hi := (37380381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431050524147 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(431050524147 / 400000000000) = 1/(100000000000 / 431050524147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15005 : Bounds (1461055121 / 1000000000) (365263781 / 250000000) (Real.log (431050524147 / 100000000000)) := by
  have h := reflection_log_15005_neg
  have he : Real.log (431050524147 / 100000000000) = -Real.log (100000000000 / 431050524147) := by
    rw [show ((431050524147 / 100000000000) : ℝ) = ((100000000000 / 431050524147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15006_neg : (1102694011 / 250000000) ≤ -Real.log (500000000000 / 41166666666667) ∧
    -Real.log (500000000000 / 41166666666667) ≤ (4410776051 / 1000000000) := by
  have h := checkLog_sound (w := (9166666666667 / 73166666666667)) (n := 12)
    (lo := (62973241 / 250000000)) (hi := (50378593 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41166666666667 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(41166666666667 / 32000000000000) = 1/(500000000000 / 41166666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15006 : Bounds (1102694011 / 250000000) (4410776051 / 1000000000) (Real.log (41166666666667 / 500000000000)) := by
  have h := reflection_log_15006_neg
  have he : Real.log (41166666666667 / 500000000000) = -Real.log (500000000000 / 41166666666667) := by
    rw [show ((41166666666667 / 500000000000) : ℝ) = ((500000000000 / 41166666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15007_neg : (1331212 / 1953125) ≤ -Real.log (1000 / 1977) ∧
    -Real.log (1000 / 1977) ≤ (136316109 / 200000000) := by
  have h := checkLog_sound (w := (977 / 2977)) (n := 12)
    (lo := (1331212 / 1953125)) (hi := (136316109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977 / 1000) = 1/(1000 / 1977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15007 : Bounds (1331212 / 1953125) (136316109 / 200000000) (Real.log (1977 / 1000)) := by
  have h := reflection_log_15007_neg
  have he : Real.log (1977 / 1000) = -Real.log (1000 / 1977) := by
    rw [show ((1977 / 1000) : ℝ) = ((1000 / 1977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15008_neg : (188613053 / 50000000) ≤ -Real.log (23 / 1000) ∧
    -Real.log (23 / 1000) ≤ (1886130533 / 500000000) := by
  have h := checkLog_sound (w := (33 / 217)) (n := 12)
    (lo := (7663129 / 25000000)) (hi := (306525161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 92) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 92) = 1/(23 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15008 : Bounds (-1886130533 / 500000000) (-188613053 / 50000000) (Real.log (23 / 1000)) := by
  have h := reflection_log_15008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15009_neg : (976523 / 1000000000) ≤ -Real.log (1000000 / 1000977) ∧
    -Real.log (1000000 / 1000977) ≤ (244131 / 250000000) := by
  have h := checkLog_sound (w := (977 / 2000977)) (n := 12)
    (lo := (976523 / 1000000000)) (hi := (244131 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000977 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000977 / 1000000) = 1/(1000000 / 1000977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15009 : Bounds (976523 / 1000000000) (244131 / 250000000) (Real.log (1000977 / 1000000)) := by
  have h := reflection_log_15009_neg
  have he : Real.log (1000977 / 1000000) = -Real.log (1000000 / 1000977) := by
    rw [show ((1000977 / 1000000) : ℝ) = ((1000000 / 1000977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15010_neg : (977477 / 1000000000) ≤ -Real.log (999023 / 1000000) ∧
    -Real.log (999023 / 1000000) ≤ (488739 / 500000000) := by
  have h := checkLog_sound (w := (977 / 1999023)) (n := 12)
    (lo := (977477 / 1000000000)) (hi := (488739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999023) = 1/(999023 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15010 : Bounds (-488739 / 500000000) (-977477 / 1000000000) (Real.log (999023 / 1000000)) := by
  have h := reflection_log_15010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15011_neg : (484118543 / 1000000000) ≤ -Real.log (125000 / 202843) ∧
    -Real.log (125000 / 202843) ≤ (30257409 / 62500000) := by
  have h := checkLog_sound (w := (77843 / 327843)) (n := 12)
    (lo := (484118543 / 1000000000)) (hi := (30257409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202843 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202843 / 125000) = 1/(125000 / 202843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15011 : Bounds (484118543 / 1000000000) (30257409 / 62500000) (Real.log (202843 / 125000)) := by
  have h := reflection_log_15011_neg
  have he : Real.log (202843 / 125000) = -Real.log (125000 / 202843) := by
    rw [show ((202843 / 125000) : ℝ) = ((125000 / 202843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15012_neg : (243707819 / 250000000) ≤ -Real.log (47157 / 125000) ∧
    -Real.log (47157 / 125000) ≤ (487415639 / 500000000) := by
  have h := checkLog_sound (w := (15343 / 109657)) (n := 12)
    (lo := (2200657 / 7812500)) (hi := (281684097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 47157) = 1/(47157 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15012 : Bounds (-487415639 / 500000000) (-243707819 / 250000000) (Real.log (47157 / 125000)) := by
  have h := reflection_log_15012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15013_neg : (485296101 / 1000000000) ≤ -Real.log (62500 / 101541) ∧
    -Real.log (62500 / 101541) ≤ (242648051 / 500000000) := by
  have h := checkLog_sound (w := (39041 / 164041)) (n := 12)
    (lo := (485296101 / 1000000000)) (hi := (242648051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101541 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101541 / 62500) = 1/(62500 / 101541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15013 : Bounds (485296101 / 1000000000) (242648051 / 500000000) (Real.log (101541 / 62500)) := by
  have h := reflection_log_15013_neg
  have he : Real.log (101541 / 62500) = -Real.log (62500 / 101541) := by
    rw [show ((101541 / 62500) : ℝ) = ((62500 / 101541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15014_neg : (979912339 / 1000000000) ≤ -Real.log (23459 / 62500) ∧
    -Real.log (23459 / 62500) ≤ (979912341 / 1000000000) := by
  have h := checkLog_sound (w := (7791 / 54709)) (n := 12)
    (lo := (286765159 / 1000000000)) (hi := (7169129 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23459) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 23459) = 1/(23459 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15014 : Bounds (-979912341 / 1000000000) (-979912339 / 1000000000) (Real.log (23459 / 62500)) := by
  have h := reflection_log_15014_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15015_neg : (494616239 / 1000000000) ≤ -Real.log (2382050319 / 3906250000) ∧
    -Real.log (2382050319 / 3906250000) ≤ (6182703 / 12500000) := by
  have h := checkLog_sound (w := (1524199681 / 6288300319)) (n := 12)
    (lo := (494616239 / 1000000000)) (hi := (6182703 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 2382050319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 2382050319) = 1/(2382050319 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15015 : Bounds (-6182703 / 12500000) (-494616239 / 1000000000) (Real.log (2382050319 / 3906250000)) := by
  have h := reflection_log_15015_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15016_neg : (490712733 / 1000000000) ≤ -Real.log (9565467351 / 15625000000) ∧
    -Real.log (9565467351 / 15625000000) ≤ (245356367 / 500000000) := by
  have h := checkLog_sound (w := (6059532649 / 25190467351)) (n := 12)
    (lo := (490712733 / 1000000000)) (hi := (245356367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 9565467351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 9565467351) = 1/(9565467351 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15016 : Bounds (-245356367 / 500000000) (-490712733 / 1000000000) (Real.log (9565467351 / 15625000000)) := by
  have h := reflection_log_15016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15017_neg : (1458949819 / 1000000000) ≤ -Real.log (250000000000 / 1075359967767) ∧
    -Real.log (250000000000 / 1075359967767) ≤ (729474911 / 500000000) := by
  have h := checkLog_sound (w := (75359967767 / 2075359967767)) (n := 12)
    (lo := (72655459 / 1000000000)) (hi := (3632773 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075359967767 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1075359967767 / 1000000000000) = 1/(250000000000 / 1075359967767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15017 : Bounds (1458949819 / 1000000000) (729474911 / 500000000) (Real.log (1075359967767 / 250000000000)) := by
  have h := reflection_log_15017_neg
  have he : Real.log (1075359967767 / 250000000000) = -Real.log (250000000000 / 1075359967767) := by
    rw [show ((1075359967767 / 250000000000) : ℝ) = ((250000000000 / 1075359967767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15018_neg : (36630211 / 25000000) ≤ -Real.log (50000000000 / 216422268639) ∧
    -Real.log (50000000000 / 216422268639) ≤ (1465208443 / 1000000000) := by
  have h := checkLog_sound (w := (16422268639 / 416422268639)) (n := 12)
    (lo := (493213 / 6250000)) (hi := (78914081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216422268639 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(216422268639 / 200000000000) = 1/(50000000000 / 216422268639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15018 : Bounds (36630211 / 25000000) (1465208443 / 1000000000) (Real.log (216422268639 / 50000000000)) := by
  have h := reflection_log_15018_neg
  have he : Real.log (216422268639 / 50000000000) = -Real.log (50000000000 / 216422268639) := by
    rw [show ((216422268639 / 50000000000) : ℝ) = ((50000000000 / 216422268639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15019_neg : (1102694011 / 250000000) ≤ -Real.log (250000000000 / 20583333333333) ∧
    -Real.log (250000000000 / 20583333333333) ≤ (4410776051 / 1000000000) := by
  have h := checkLog_sound (w := (4583333333333 / 36583333333333)) (n := 12)
    (lo := (62973241 / 250000000)) (hi := (50378593 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20583333333333 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20583333333333 / 16000000000000) = 1/(250000000000 / 20583333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15019 : Bounds (1102694011 / 250000000) (4410776051 / 1000000000) (Real.log (20583333333333 / 250000000000)) := by
  have h := reflection_log_15019_neg
  have he : Real.log (20583333333333 / 250000000000) = -Real.log (250000000000 / 20583333333333) := by
    rw [show ((20583333333333 / 250000000000) : ℝ) = ((250000000000 / 20583333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15020_neg : (4453841603 / 1000000000) ≤ -Real.log (250000000000 / 21489130434783) ∧
    -Real.log (250000000000 / 21489130434783) ≤ (445384161 / 100000000) := by
  have h := checkLog_sound (w := (5489130434783 / 37489130434783)) (n := 12)
    (lo := (294958523 / 1000000000)) (hi := (73739631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21489130434783 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(21489130434783 / 16000000000000) = 1/(250000000000 / 21489130434783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15020 : Bounds (4453841603 / 1000000000) (445384161 / 100000000) (Real.log (21489130434783 / 250000000000)) := by
  have h := reflection_log_15020_neg
  have he : Real.log (21489130434783 / 250000000000) = -Real.log (250000000000 / 21489130434783) := by
    rw [show ((21489130434783 / 250000000000) : ℝ) = ((250000000000 / 21489130434783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15021_neg : (682086233 / 1000000000) ≤ -Real.log (500 / 989) ∧
    -Real.log (500 / 989) ≤ (341043117 / 500000000) := by
  have h := checkLog_sound (w := (489 / 1489)) (n := 12)
    (lo := (682086233 / 1000000000)) (hi := (341043117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989 / 500) = 1/(500 / 989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15021 : Bounds (682086233 / 1000000000) (341043117 / 500000000) (Real.log (989 / 500)) := by
  have h := reflection_log_15021_neg
  have he : Real.log (989 / 500) = -Real.log (500 / 989) := by
    rw [show ((989 / 500) : ℝ) = ((500 / 989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15022_neg : (1908356411 / 500000000) ≤ -Real.log (11 / 500) ∧
    -Real.log (11 / 500) ≤ (954178207 / 250000000) := by
  have h := checkLog_sound (w := (37 / 213)) (n := 12)
    (lo := (175488461 / 500000000)) (hi := (350976923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 88) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 88) = 1/(11 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15022 : Bounds (-954178207 / 250000000) (-1908356411 / 500000000) (Real.log (11 / 500)) := by
  have h := reflection_log_15022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15023_neg : (488761 / 500000000) ≤ -Real.log (500000 / 500489) ∧
    -Real.log (500000 / 500489) ≤ (977523 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 1000489)) (n := 12)
    (lo := (488761 / 500000000)) (hi := (977523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500489 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500489 / 500000) = 1/(500000 / 500489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15023 : Bounds (488761 / 500000000) (977523 / 1000000000) (Real.log (500489 / 500000)) := by
  have h := reflection_log_15023_neg
  have he : Real.log (500489 / 500000) = -Real.log (500000 / 500489) := by
    rw [show ((500489 / 500000) : ℝ) = ((500000 / 500489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15024_neg : (489239 / 500000000) ≤ -Real.log (499511 / 500000) ∧
    -Real.log (499511 / 500000) ≤ (978479 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 999511)) (n := 12)
    (lo := (489239 / 500000000)) (hi := (978479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499511) = 1/(499511 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15024 : Bounds (-978479 / 1000000000) (-489239 / 500000000) (Real.log (499511 / 500000)) := by
  have h := reflection_log_15024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15025_neg : (242450123 / 500000000) ≤ -Real.log (1000000 / 1624013) ∧
    -Real.log (1000000 / 1624013) ≤ (484900247 / 1000000000) := by
  have h := checkLog_sound (w := (624013 / 2624013)) (n := 12)
    (lo := (242450123 / 500000000)) (hi := (484900247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1624013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1624013 / 1000000) = 1/(1000000 / 1624013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15025 : Bounds (242450123 / 500000000) (484900247 / 1000000000) (Real.log (1624013 / 1000000)) := by
  have h := reflection_log_15025_neg
  have he : Real.log (1624013 / 1000000) = -Real.log (1000000 / 1624013) := by
    rw [show ((1624013 / 1000000) : ℝ) = ((1000000 / 1624013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15026_neg : (97820071 / 100000000) ≤ -Real.log (375987 / 1000000) ∧
    -Real.log (375987 / 1000000) ≤ (122275089 / 125000000) := by
  have h := checkLog_sound (w := (124013 / 875987)) (n := 12)
    (lo := (28505353 / 100000000)) (hi := (285053531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375987) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 375987) = 1/(375987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15026 : Bounds (-122275089 / 125000000) (-97820071 / 100000000) (Real.log (375987 / 1000000)) := by
  have h := reflection_log_15026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15027_neg : (486082419 / 1000000000) ≤ -Real.log (500000 / 812967) ∧
    -Real.log (500000 / 812967) ≤ (24304121 / 50000000) := by
  have h := checkLog_sound (w := (312967 / 1312967)) (n := 12)
    (lo := (486082419 / 1000000000)) (hi := (24304121 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((812967 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(812967 / 500000) = 1/(500000 / 812967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15027 : Bounds (486082419 / 1000000000) (24304121 / 50000000) (Real.log (812967 / 500000)) := by
  have h := reflection_log_15027_neg
  have he : Real.log (812967 / 500000) = -Real.log (500000 / 812967) := by
    rw [show ((812967 / 500000) : ℝ) = ((500000 / 812967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15028_neg : (39332921 / 40000000) ≤ -Real.log (187033 / 500000) ∧
    -Real.log (187033 / 500000) ≤ (983323027 / 1000000000) := by
  have h := checkLog_sound (w := (62967 / 437033)) (n := 12)
    (lo := (58035169 / 200000000)) (hi := (145087923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187033) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 187033) = 1/(187033 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15028 : Bounds (-983323027 / 1000000000) (-39332921 / 40000000) (Real.log (187033 / 500000)) := by
  have h := reflection_log_15028_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15029_neg : (248620303 / 500000000) ≤ -Real.log (152051656911 / 250000000000) ∧
    -Real.log (152051656911 / 250000000000) ≤ (497240607 / 1000000000) := by
  have h := checkLog_sound (w := (97948343089 / 402051656911)) (n := 12)
    (lo := (248620303 / 500000000)) (hi := (497240607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 152051656911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 152051656911) = 1/(152051656911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15029 : Bounds (-497240607 / 1000000000) (-248620303 / 500000000) (Real.log (152051656911 / 250000000000)) := by
  have h := reflection_log_15029_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15030_neg : (30831279 / 62500000) ≤ -Real.log (610607775831 / 1000000000000) ∧
    -Real.log (610607775831 / 1000000000000) ≤ (98660093 / 200000000) := by
  have h := checkLog_sound (w := (389392224169 / 1610607775831)) (n := 12)
    (lo := (30831279 / 62500000)) (hi := (98660093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 610607775831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 610607775831) = 1/(610607775831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15030 : Bounds (-98660093 / 200000000) (-30831279 / 62500000) (Real.log (610607775831 / 1000000000000)) := by
  have h := reflection_log_15030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15031_neg : (365775239 / 250000000) ≤ -Real.log (500000000000 / 2159666424637) ∧
    -Real.log (500000000000 / 2159666424637) ≤ (1463100959 / 1000000000) := by
  have h := checkLog_sound (w := (159666424637 / 4159666424637)) (n := 12)
    (lo := (19201649 / 250000000)) (hi := (76806597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2159666424637 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2159666424637 / 2000000000000) = 1/(500000000000 / 2159666424637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15031 : Bounds (365775239 / 250000000) (1463100959 / 1000000000) (Real.log (2159666424637 / 500000000000)) := by
  have h := reflection_log_15031_neg
  have he : Real.log (2159666424637 / 500000000000) = -Real.log (500000000000 / 2159666424637) := by
    rw [show ((2159666424637 / 500000000000) : ℝ) = ((500000000000 / 2159666424637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15032_neg : (293881089 / 200000000) ≤ -Real.log (125000000000 / 543331257051) ∧
    -Real.log (125000000000 / 543331257051) ≤ (183675681 / 125000000) := by
  have h := checkLog_sound (w := (43331257051 / 1043331257051)) (n := 12)
    (lo := (16622217 / 200000000)) (hi := (41555543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543331257051 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(543331257051 / 500000000000) = 1/(125000000000 / 543331257051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15032 : Bounds (293881089 / 200000000) (183675681 / 125000000) (Real.log (543331257051 / 125000000000)) := by
  have h := reflection_log_15032_neg
  have he : Real.log (543331257051 / 125000000000) = -Real.log (125000000000 / 543331257051) := by
    rw [show ((543331257051 / 125000000000) : ℝ) = ((125000000000 / 543331257051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15033_neg : (4453841603 / 1000000000) ≤ -Real.log (100000000000 / 8595652173913) ∧
    -Real.log (100000000000 / 8595652173913) ≤ (445384161 / 100000000) := by
  have h := checkLog_sound (w := (2195652173913 / 14995652173913)) (n := 12)
    (lo := (294958523 / 1000000000)) (hi := (73739631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8595652173913 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8595652173913 / 6400000000000) = 1/(100000000000 / 8595652173913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15033 : Bounds (4453841603 / 1000000000) (445384161 / 100000000) (Real.log (8595652173913 / 100000000000)) := by
  have h := reflection_log_15033_neg
  have he : Real.log (8595652173913 / 100000000000) = -Real.log (100000000000 / 8595652173913) := by
    rw [show ((8595652173913 / 100000000000) : ℝ) = ((100000000000 / 8595652173913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15034_neg : (899759811 / 200000000) ≤ -Real.log (250000000000 / 22477272727273) ∧
    -Real.log (250000000000 / 22477272727273) ≤ (2249399531 / 500000000) := by
  have h := checkLog_sound (w := (6477272727273 / 38477272727273)) (n := 12)
    (lo := (13596639 / 40000000)) (hi := (42489497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22477272727273 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(22477272727273 / 16000000000000) = 1/(250000000000 / 22477272727273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15034 : Bounds (899759811 / 200000000) (2249399531 / 500000000) (Real.log (22477272727273 / 250000000000)) := by
  have h := reflection_log_15034_neg
  have he : Real.log (22477272727273 / 250000000000) = -Real.log (250000000000 / 22477272727273) := by
    rw [show ((22477272727273 / 250000000000) : ℝ) = ((250000000000 / 22477272727273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15035_neg : (341295833 / 500000000) ≤ -Real.log (1000 / 1979) ∧
    -Real.log (1000 / 1979) ≤ (682591667 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 2979)) (n := 12)
    (lo := (341295833 / 500000000)) (hi := (682591667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979 / 1000) = 1/(1000 / 1979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15035 : Bounds (341295833 / 500000000) (682591667 / 1000000000) (Real.log (1979 / 1000)) := by
  have h := reflection_log_15035_neg
  have he : Real.log (1979 / 1000) = -Real.log (1000 / 1979) := by
    rw [show ((1979 / 1000) : ℝ) = ((1000 / 1979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15036_neg : (1931616419 / 500000000) ≤ -Real.log (21 / 1000) ∧
    -Real.log (21 / 1000) ≤ (965808211 / 250000000) := by
  have h := checkLog_sound (w := (41 / 209)) (n := 12)
    (lo := (198748469 / 500000000)) (hi := (397496939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 84) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 84) = 1/(21 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15036 : Bounds (-965808211 / 250000000) (-1931616419 / 500000000) (Real.log (21 / 1000)) := by
  have h := reflection_log_15036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15037_neg : (978521 / 1000000000) ≤ -Real.log (1000000 / 1000979) ∧
    -Real.log (1000000 / 1000979) ≤ (489261 / 500000000) := by
  have h := checkLog_sound (w := (979 / 2000979)) (n := 12)
    (lo := (978521 / 1000000000)) (hi := (489261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000979 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000979 / 1000000) = 1/(1000000 / 1000979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15037 : Bounds (978521 / 1000000000) (489261 / 500000000) (Real.log (1000979 / 1000000)) := by
  have h := reflection_log_15037_neg
  have he : Real.log (1000979 / 1000000) = -Real.log (1000000 / 1000979) := by
    rw [show ((1000979 / 1000000) : ℝ) = ((1000000 / 1000979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15038_neg : (979479 / 1000000000) ≤ -Real.log (999021 / 1000000) ∧
    -Real.log (999021 / 1000000) ≤ (24487 / 25000000) := by
  have h := checkLog_sound (w := (979 / 1999021)) (n := 12)
    (lo := (979479 / 1000000000)) (hi := (24487 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999021) = 1/(999021 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15038 : Bounds (-24487 / 25000000) (-979479 / 1000000000) (Real.log (999021 / 1000000)) := by
  have h := reflection_log_15038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15039_neg : (485687491 / 1000000000) ≤ -Real.log (250000 / 406323) ∧
    -Real.log (250000 / 406323) ≤ (121421873 / 250000000) := by
  have h := checkLog_sound (w := (156323 / 656323)) (n := 12)
    (lo := (485687491 / 1000000000)) (hi := (121421873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((406323 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(406323 / 250000) = 1/(250000 / 406323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15039 : Bounds (485687491 / 1000000000) (121421873 / 250000000) (Real.log (406323 / 250000)) := by
  have h := reflection_log_15039_neg
  have he : Real.log (406323 / 250000) = -Real.log (250000 / 406323) := by
    rw [show ((406323 / 250000) : ℝ) = ((250000 / 406323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
