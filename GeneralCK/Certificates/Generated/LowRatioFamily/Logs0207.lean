import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13248_neg : (733927303 / 1000000000) ≤ -Real.log (500000000000 / 1041623051581) ∧
    -Real.log (500000000000 / 1041623051581) ≤ (146785461 / 200000000) := by
  have h := checkLog_sound (w := (41623051581 / 2041623051581)) (n := 12)
    (lo := (40780123 / 1000000000)) (hi := (10195031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1041623051581 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1041623051581 / 1000000000000) = 1/(500000000000 / 1041623051581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13248 : Bounds (733927303 / 1000000000) (146785461 / 200000000) (Real.log (1041623051581 / 500000000000)) := by
  have h := reflection_log_13248_neg
  have he : Real.log (1041623051581 / 500000000000) = -Real.log (500000000000 / 1041623051581) := by
    rw [show ((1041623051581 / 500000000000) : ℝ) = ((500000000000 / 1041623051581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13249_neg : (36984371 / 50000000) ≤ -Real.log (500000000000 / 1047640235551) ∧
    -Real.log (500000000000 / 1047640235551) ≤ (369843711 / 500000000) := by
  have h := checkLog_sound (w := (47640235551 / 2047640235551)) (n := 12)
    (lo := (581753 / 12500000)) (hi := (46540241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1047640235551 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1047640235551 / 1000000000000) = 1/(500000000000 / 1047640235551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13249 : Bounds (36984371 / 50000000) (369843711 / 500000000) (Real.log (1047640235551 / 500000000000)) := by
  have h := reflection_log_13249_neg
  have he : Real.log (1047640235551 / 500000000000) = -Real.log (500000000000 / 1047640235551) := by
    rw [show ((1047640235551 / 500000000000) : ℝ) = ((500000000000 / 1047640235551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13250_neg : (96265167 / 62500000) ≤ -Real.log (500000000000 / 2332861189801) ∧
    -Real.log (500000000000 / 2332861189801) ≤ (61609707 / 40000000) := by
  have h := checkLog_sound (w := (332861189801 / 4332861189801)) (n := 12)
    (lo := (19243539 / 125000000)) (hi := (153948313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2332861189801 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2332861189801 / 2000000000000) = 1/(500000000000 / 2332861189801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13250 : Bounds (96265167 / 62500000) (61609707 / 40000000) (Real.log (2332861189801 / 500000000000)) := by
  have h := reflection_log_13250_neg
  have he : Real.log (2332861189801 / 500000000000) = -Real.log (500000000000 / 2332861189801) := by
    rw [show ((2332861189801 / 500000000000) : ℝ) = ((500000000000 / 2332861189801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13251_neg : (1550597411 / 1000000000) ≤ -Real.log (500000000000 / 2357142857143) ∧
    -Real.log (500000000000 / 2357142857143) ≤ (775298707 / 500000000) := by
  have h := checkLog_sound (w := (357142857143 / 4357142857143)) (n := 12)
    (lo := (164303051 / 1000000000)) (hi := (41075763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2357142857143 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2357142857143 / 2000000000000) = 1/(500000000000 / 2357142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13251 : Bounds (1550597411 / 1000000000) (775298707 / 500000000) (Real.log (2357142857143 / 500000000000)) := by
  have h := reflection_log_13251_neg
  have he : Real.log (2357142857143 / 500000000000) = -Real.log (500000000000 / 2357142857143) := by
    rw [show ((2357142857143 / 500000000000) : ℝ) = ((500000000000 / 2357142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13252_neg : (251295909 / 500000000) ≤ -Real.log (1000 / 1653) ∧
    -Real.log (1000 / 1653) ≤ (502591819 / 1000000000) := by
  have h := checkLog_sound (w := (653 / 2653)) (n := 12)
    (lo := (251295909 / 500000000)) (hi := (502591819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1653 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1653 / 1000) = 1/(1000 / 1653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13252 : Bounds (251295909 / 500000000) (502591819 / 1000000000) (Real.log (1653 / 1000)) := by
  have h := reflection_log_13252_neg
  have he : Real.log (1653 / 1000) = -Real.log (1000 / 1653) := by
    rw [show ((1653 / 1000) : ℝ) = ((1000 / 1653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13253_neg : (529215249 / 500000000) ≤ -Real.log (347 / 1000) ∧
    -Real.log (347 / 1000) ≤ (2116861 / 2000000) := by
  have h := checkLog_sound (w := (153 / 847)) (n := 12)
    (lo := (182641659 / 500000000)) (hi := (365283319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 347) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 347) = 1/(347 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13253 : Bounds (-2116861 / 2000000) (-529215249 / 500000000) (Real.log (347 / 1000)) := by
  have h := reflection_log_13253_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13254_neg : (326393 / 500000000) ≤ -Real.log (1000000 / 1000653) ∧
    -Real.log (1000000 / 1000653) ≤ (652787 / 1000000000) := by
  have h := checkLog_sound (w := (653 / 2000653)) (n := 12)
    (lo := (326393 / 500000000)) (hi := (652787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000653 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000653 / 1000000) = 1/(1000000 / 1000653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13254 : Bounds (326393 / 500000000) (652787 / 1000000000) (Real.log (1000653 / 1000000)) := by
  have h := reflection_log_13254_neg
  have he : Real.log (1000653 / 1000000) = -Real.log (1000000 / 1000653) := by
    rw [show ((1000653 / 1000000) : ℝ) = ((1000000 / 1000653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13255_neg : (653213 / 1000000000) ≤ -Real.log (999347 / 1000000) ∧
    -Real.log (999347 / 1000000) ≤ (326607 / 500000000) := by
  have h := checkLog_sound (w := (653 / 1999347)) (n := 12)
    (lo := (653213 / 1000000000)) (hi := (326607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999347) = 1/(999347 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13255 : Bounds (-326607 / 500000000) (-653213 / 1000000000) (Real.log (999347 / 1000000)) := by
  have h := reflection_log_13255_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13256_neg : (151261573 / 500000000) ≤ -Real.log (1000000 / 1353269) ∧
    -Real.log (1000000 / 1353269) ≤ (302523147 / 1000000000) := by
  have h := checkLog_sound (w := (353269 / 2353269)) (n := 12)
    (lo := (151261573 / 500000000)) (hi := (302523147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353269 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1353269 / 1000000) = 1/(1000000 / 1353269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13256 : Bounds (151261573 / 500000000) (302523147 / 1000000000) (Real.log (1353269 / 1000000)) := by
  have h := reflection_log_13256_neg
  have he : Real.log (1353269 / 1000000) = -Real.log (1000000 / 1353269) := by
    rw [show ((1353269 / 1000000) : ℝ) = ((1000000 / 1353269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13257_neg : (108956209 / 250000000) ≤ -Real.log (646731 / 1000000) ∧
    -Real.log (646731 / 1000000) ≤ (435824837 / 1000000000) := by
  have h := checkLog_sound (w := (353269 / 1646731)) (n := 12)
    (lo := (108956209 / 250000000)) (hi := (435824837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 646731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 646731) = 1/(646731 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13257 : Bounds (-435824837 / 1000000000) (-108956209 / 250000000) (Real.log (646731 / 1000000)) := by
  have h := reflection_log_13257_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13258_neg : (76097737 / 250000000) ≤ -Real.log (1000000 / 1355799) ∧
    -Real.log (1000000 / 1355799) ≤ (304390949 / 1000000000) := by
  have h := checkLog_sound (w := (355799 / 2355799)) (n := 12)
    (lo := (76097737 / 250000000)) (hi := (304390949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1355799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1355799 / 1000000) = 1/(1000000 / 1355799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13258 : Bounds (76097737 / 250000000) (304390949 / 1000000000) (Real.log (1355799 / 1000000)) := by
  have h := reflection_log_13258_neg
  have he : Real.log (1355799 / 1000000) = -Real.log (1000000 / 1355799) := by
    rw [show ((1355799 / 1000000) : ℝ) = ((1000000 / 1355799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13259_neg : (439744489 / 1000000000) ≤ -Real.log (644201 / 1000000) ∧
    -Real.log (644201 / 1000000) ≤ (43974449 / 100000000) := by
  have h := checkLog_sound (w := (355799 / 1644201)) (n := 12)
    (lo := (439744489 / 1000000000)) (hi := (43974449 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 644201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 644201) = 1/(644201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13259 : Bounds (-43974449 / 100000000) (-439744489 / 1000000000) (Real.log (644201 / 1000000)) := by
  have h := reflection_log_13259_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13260_neg : (135353541 / 1000000000) ≤ -Real.log (873407071599 / 1000000000000) ∧
    -Real.log (873407071599 / 1000000000000) ≤ (67676771 / 500000000) := by
  have h := checkLog_sound (w := (126592928401 / 1873407071599)) (n := 12)
    (lo := (135353541 / 1000000000)) (hi := (67676771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 873407071599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 873407071599) = 1/(873407071599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13260 : Bounds (-67676771 / 500000000) (-135353541 / 1000000000) (Real.log (873407071599 / 1000000000000)) := by
  have h := reflection_log_13260_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13261_neg : (133301689 / 1000000000) ≤ -Real.log (875201013639 / 1000000000000) ∧
    -Real.log (875201013639 / 1000000000000) ≤ (13330169 / 100000000) := by
  have h := checkLog_sound (w := (124798986361 / 1875201013639)) (n := 12)
    (lo := (133301689 / 1000000000)) (hi := (13330169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 875201013639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 875201013639) = 1/(875201013639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13261 : Bounds (-13330169 / 100000000) (-133301689 / 1000000000) (Real.log (875201013639 / 1000000000000)) := by
  have h := reflection_log_13261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13262_neg : (369173991 / 500000000) ≤ -Real.log (250000000000 / 523118962907) ∧
    -Real.log (250000000000 / 523118962907) ≤ (46146749 / 62500000) := by
  have h := checkLog_sound (w := (23118962907 / 1023118962907)) (n := 12)
    (lo := (22600401 / 500000000)) (hi := (45200803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((523118962907 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(523118962907 / 500000000000) = 1/(250000000000 / 523118962907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13262 : Bounds (369173991 / 500000000) (46146749 / 62500000) (Real.log (523118962907 / 250000000000)) := by
  have h := reflection_log_13262_neg
  have he : Real.log (523118962907 / 250000000000) = -Real.log (250000000000 / 523118962907) := by
    rw [show ((523118962907 / 250000000000) : ℝ) = ((250000000000 / 523118962907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13263_neg : (744135437 / 1000000000) ≤ -Real.log (500000000000 / 1052310536619) ∧
    -Real.log (500000000000 / 1052310536619) ≤ (744135439 / 1000000000) := by
  have h := checkLog_sound (w := (52310536619 / 2052310536619)) (n := 12)
    (lo := (50988257 / 1000000000)) (hi := (25494129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1052310536619 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1052310536619 / 1000000000000) = 1/(500000000000 / 1052310536619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13263 : Bounds (744135437 / 1000000000) (744135439 / 1000000000) (Real.log (1052310536619 / 500000000000)) := by
  have h := reflection_log_13263_neg
  have he : Real.log (1052310536619 / 500000000000) = -Real.log (500000000000 / 1052310536619) := by
    rw [show ((1052310536619 / 500000000000) : ℝ) = ((500000000000 / 1052310536619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13264_neg : (1550597411 / 1000000000) ≤ -Real.log (250000000000 / 1178571428571) ∧
    -Real.log (250000000000 / 1178571428571) ≤ (775298707 / 500000000) := by
  have h := checkLog_sound (w := (178571428571 / 2178571428571)) (n := 12)
    (lo := (164303051 / 1000000000)) (hi := (41075763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178571428571 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1178571428571 / 1000000000000) = 1/(250000000000 / 1178571428571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13264 : Bounds (1550597411 / 1000000000) (775298707 / 500000000) (Real.log (1178571428571 / 250000000000)) := by
  have h := reflection_log_13264_neg
  have he : Real.log (1178571428571 / 250000000000) = -Real.log (250000000000 / 1178571428571) := by
    rw [show ((1178571428571 / 250000000000) : ℝ) = ((250000000000 / 1178571428571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13265_neg : (390255579 / 250000000) ≤ -Real.log (125000000000 / 595461095101) ∧
    -Real.log (125000000000 / 595461095101) ≤ (1561022319 / 1000000000) := by
  have h := checkLog_sound (w := (95461095101 / 1095461095101)) (n := 12)
    (lo := (43681989 / 250000000)) (hi := (174727957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595461095101 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(595461095101 / 500000000000) = 1/(125000000000 / 595461095101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13265 : Bounds (390255579 / 250000000) (1561022319 / 1000000000) (Real.log (595461095101 / 125000000000)) := by
  have h := reflection_log_13265_neg
  have he : Real.log (595461095101 / 125000000000) = -Real.log (125000000000 / 595461095101) := by
    rw [show ((595461095101 / 125000000000) : ℝ) = ((125000000000 / 595461095101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13266_neg : (100881011 / 200000000) ≤ -Real.log (125 / 207) ∧
    -Real.log (125 / 207) ≤ (7881329 / 15625000) := by
  have h := checkLog_sound (w := (41 / 166)) (n := 12)
    (lo := (100881011 / 200000000)) (hi := (7881329 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(207 / 125) = 1/(125 / 207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13266 : Bounds (100881011 / 200000000) (7881329 / 15625000) (Real.log (207 / 125)) := by
  have h := reflection_log_13266_neg
  have he : Real.log (207 / 125) = -Real.log (125 / 207) := by
    rw [show ((207 / 125) : ℝ) = ((125 / 207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13267_neg : (1067113621 / 1000000000) ≤ -Real.log (43 / 125) ∧
    -Real.log (43 / 125) ≤ (1067113623 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 211)) (n := 12)
    (lo := (373966441 / 1000000000)) (hi := (186983221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 86) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 86) = 1/(43 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13267 : Bounds (-1067113623 / 1000000000) (-1067113621 / 1000000000) (Real.log (43 / 125)) := by
  have h := reflection_log_13267_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13268_neg : (81973 / 125000000) ≤ -Real.log (62500 / 62541) ∧
    -Real.log (62500 / 62541) ≤ (131157 / 200000000) := by
  have h := checkLog_sound (w := (41 / 125041)) (n := 12)
    (lo := (81973 / 125000000)) (hi := (131157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62541 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62541 / 62500) = 1/(62500 / 62541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13268 : Bounds (81973 / 125000000) (131157 / 200000000) (Real.log (62541 / 62500)) := by
  have h := reflection_log_13268_neg
  have he : Real.log (62541 / 62500) = -Real.log (62500 / 62541) := by
    rw [show ((62541 / 62500) : ℝ) = ((62500 / 62541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13269_neg : (131243 / 200000000) ≤ -Real.log (62459 / 62500) ∧
    -Real.log (62459 / 62500) ≤ (82027 / 125000000) := by
  have h := checkLog_sound (w := (41 / 124959)) (n := 12)
    (lo := (131243 / 200000000)) (hi := (82027 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62459) = 1/(62459 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13269 : Bounds (-82027 / 125000000) (-131243 / 200000000) (Real.log (62459 / 62500)) := by
  have h := reflection_log_13269_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13270_neg : (303956423 / 1000000000) ≤ -Real.log (100000 / 135521) ∧
    -Real.log (100000 / 135521) ≤ (37994553 / 125000000) := by
  have h := checkLog_sound (w := (35521 / 235521)) (n := 12)
    (lo := (303956423 / 1000000000)) (hi := (37994553 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135521 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135521 / 100000) = 1/(100000 / 135521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13270 : Bounds (303956423 / 1000000000) (37994553 / 125000000) (Real.log (135521 / 100000)) := by
  have h := reflection_log_13270_neg
  have he : Real.log (135521 / 100000) = -Real.log (100000 / 135521) := by
    rw [show ((135521 / 100000) : ℝ) = ((100000 / 135521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13271_neg : (109707649 / 250000000) ≤ -Real.log (64479 / 100000) ∧
    -Real.log (64479 / 100000) ≤ (438830597 / 1000000000) := by
  have h := checkLog_sound (w := (35521 / 164479)) (n := 12)
    (lo := (109707649 / 250000000)) (hi := (438830597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 64479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 64479) = 1/(64479 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13271 : Bounds (-438830597 / 1000000000) (-109707649 / 250000000) (Real.log (64479 / 100000)) := by
  have h := reflection_log_13271_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13272_neg : (76456861 / 250000000) ≤ -Real.log (250000 / 339437) ∧
    -Real.log (250000 / 339437) ≤ (61165489 / 200000000) := by
  have h := checkLog_sound (w := (89437 / 589437)) (n := 12)
    (lo := (76456861 / 250000000)) (hi := (61165489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339437 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339437 / 250000) = 1/(250000 / 339437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13272 : Bounds (76456861 / 250000000) (61165489 / 200000000) (Real.log (339437 / 250000)) := by
  have h := reflection_log_13272_neg
  have he : Real.log (339437 / 250000) = -Real.log (250000 / 339437) := by
    rw [show ((339437 / 250000) : ℝ) = ((250000 / 339437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13273_neg : (864794 / 1953125) ≤ -Real.log (160563 / 250000) ∧
    -Real.log (160563 / 250000) ≤ (442774529 / 1000000000) := by
  have h := checkLog_sound (w := (89437 / 410563)) (n := 12)
    (lo := (864794 / 1953125)) (hi := (442774529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 160563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 160563) = 1/(160563 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13273 : Bounds (-442774529 / 1000000000) (-864794 / 1953125) (Real.log (160563 / 250000)) := by
  have h := reflection_log_13273_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13274_neg : (34236771 / 250000000) ≤ -Real.log (54501023031 / 62500000000) ∧
    -Real.log (54501023031 / 62500000000) ≤ (27389417 / 200000000) := by
  have h := checkLog_sound (w := (7998976969 / 117001023031)) (n := 12)
    (lo := (34236771 / 250000000)) (hi := (27389417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 54501023031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 54501023031) = 1/(54501023031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13274 : Bounds (-27389417 / 200000000) (-34236771 / 250000000) (Real.log (54501023031 / 62500000000)) := by
  have h := reflection_log_13274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13275_neg : (33718543 / 250000000) ≤ -Real.log (8738258559 / 10000000000) ∧
    -Real.log (8738258559 / 10000000000) ≤ (134874173 / 1000000000) := by
  have h := checkLog_sound (w := (1261741441 / 18738258559)) (n := 12)
    (lo := (33718543 / 250000000)) (hi := (134874173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 8738258559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 8738258559) = 1/(8738258559 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13275 : Bounds (-134874173 / 1000000000) (-33718543 / 250000000) (Real.log (8738258559 / 10000000000)) := by
  have h := reflection_log_13275_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13276_neg : (742787019 / 1000000000) ≤ -Real.log (100000000000 / 210178507731) ∧
    -Real.log (100000000000 / 210178507731) ≤ (742787021 / 1000000000) := by
  have h := checkLog_sound (w := (10178507731 / 410178507731)) (n := 12)
    (lo := (49639839 / 1000000000)) (hi := (310249 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210178507731 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(210178507731 / 200000000000) = 1/(100000000000 / 210178507731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13276 : Bounds (742787019 / 1000000000) (742787021 / 1000000000) (Real.log (210178507731 / 100000000000)) := by
  have h := reflection_log_13276_neg
  have he : Real.log (210178507731 / 100000000000) = -Real.log (100000000000 / 210178507731) := by
    rw [show ((210178507731 / 100000000000) : ℝ) = ((100000000000 / 210178507731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13277_neg : (748601973 / 1000000000) ≤ -Real.log (250000000000 / 528510615771) ∧
    -Real.log (250000000000 / 528510615771) ≤ (29944079 / 40000000) := by
  have h := checkLog_sound (w := (28510615771 / 1028510615771)) (n := 12)
    (lo := (55454793 / 1000000000)) (hi := (27727397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528510615771 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(528510615771 / 500000000000) = 1/(250000000000 / 528510615771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13277 : Bounds (748601973 / 1000000000) (29944079 / 40000000) (Real.log (528510615771 / 250000000000)) := by
  have h := reflection_log_13277_neg
  have he : Real.log (528510615771 / 250000000000) = -Real.log (250000000000 / 528510615771) := by
    rw [show ((528510615771 / 250000000000) : ℝ) = ((250000000000 / 528510615771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13278_neg : (390255579 / 250000000) ≤ -Real.log (500000000000 / 2381844380403) ∧
    -Real.log (500000000000 / 2381844380403) ≤ (1561022319 / 1000000000) := by
  have h := checkLog_sound (w := (381844380403 / 4381844380403)) (n := 12)
    (lo := (43681989 / 250000000)) (hi := (174727957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2381844380403 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2381844380403 / 2000000000000) = 1/(500000000000 / 2381844380403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13278 : Bounds (390255579 / 250000000) (1561022319 / 1000000000) (Real.log (2381844380403 / 500000000000)) := by
  have h := reflection_log_13278_neg
  have he : Real.log (2381844380403 / 500000000000) = -Real.log (500000000000 / 2381844380403) := by
    rw [show ((2381844380403 / 500000000000) : ℝ) = ((500000000000 / 2381844380403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13279_neg : (392879669 / 250000000) ≤ -Real.log (500000000000 / 2406976744187) ∧
    -Real.log (500000000000 / 2406976744187) ≤ (1571518679 / 1000000000) := by
  have h := checkLog_sound (w := (406976744187 / 4406976744187)) (n := 12)
    (lo := (46306079 / 250000000)) (hi := (185224317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2406976744187 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2406976744187 / 2000000000000) = 1/(500000000000 / 2406976744187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13279 : Bounds (392879669 / 250000000) (1571518679 / 1000000000) (Real.log (2406976744187 / 500000000000)) := by
  have h := reflection_log_13279_neg
  have he : Real.log (2406976744187 / 500000000000) = -Real.log (500000000000 / 2406976744187) := by
    rw [show ((2406976744187 / 500000000000) : ℝ) = ((500000000000 / 2406976744187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13280_neg : (506215011 / 1000000000) ≤ -Real.log (1000 / 1659) ∧
    -Real.log (1000 / 1659) ≤ (126553753 / 250000000) := by
  have h := checkLog_sound (w := (659 / 2659)) (n := 12)
    (lo := (506215011 / 1000000000)) (hi := (126553753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1659 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1659 / 1000) = 1/(1000 / 1659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13280 : Bounds (506215011 / 1000000000) (126553753 / 250000000) (Real.log (1659 / 1000)) := by
  have h := reflection_log_13280_neg
  have he : Real.log (1659 / 1000) = -Real.log (1000 / 1659) := by
    rw [show ((1659 / 1000) : ℝ) = ((1000 / 1659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13281_neg : (1075872801 / 1000000000) ≤ -Real.log (341 / 1000) ∧
    -Real.log (341 / 1000) ≤ (1075872803 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 841)) (n := 12)
    (lo := (382725621 / 1000000000)) (hi := (191362811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 341) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 341) = 1/(341 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13281 : Bounds (-1075872803 / 1000000000) (-1075872801 / 1000000000) (Real.log (341 / 1000)) := by
  have h := reflection_log_13281_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13282_neg : (329391 / 500000000) ≤ -Real.log (1000000 / 1000659) ∧
    -Real.log (1000000 / 1000659) ≤ (658783 / 1000000000) := by
  have h := checkLog_sound (w := (659 / 2000659)) (n := 12)
    (lo := (329391 / 500000000)) (hi := (658783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000659 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000659 / 1000000) = 1/(1000000 / 1000659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13282 : Bounds (329391 / 500000000) (658783 / 1000000000) (Real.log (1000659 / 1000000)) := by
  have h := reflection_log_13282_neg
  have he : Real.log (1000659 / 1000000) = -Real.log (1000000 / 1000659) := by
    rw [show ((1000659 / 1000000) : ℝ) = ((1000000 / 1000659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13283_neg : (659217 / 1000000000) ≤ -Real.log (999341 / 1000000) ∧
    -Real.log (999341 / 1000000) ≤ (329609 / 500000000) := by
  have h := checkLog_sound (w := (659 / 1999341)) (n := 12)
    (lo := (659217 / 1000000000)) (hi := (329609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999341) = 1/(999341 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13283 : Bounds (-329609 / 500000000) (-659217 / 1000000000) (Real.log (999341 / 1000000)) := by
  have h := reflection_log_13283_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13284_neg : (30539207 / 100000000) ≤ -Real.log (1000000 / 1357157) ∧
    -Real.log (1000000 / 1357157) ≤ (305392071 / 1000000000) := by
  have h := checkLog_sound (w := (357157 / 2357157)) (n := 12)
    (lo := (30539207 / 100000000)) (hi := (305392071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1357157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1357157 / 1000000) = 1/(1000000 / 1357157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13284 : Bounds (30539207 / 100000000) (305392071 / 1000000000) (Real.log (1357157 / 1000000)) := by
  have h := reflection_log_13284_neg
  have he : Real.log (1357157 / 1000000) = -Real.log (1000000 / 1357157) := by
    rw [show ((1357157 / 1000000) : ℝ) = ((1000000 / 1357157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13285_neg : (13807961 / 31250000) ≤ -Real.log (642843 / 1000000) ∧
    -Real.log (642843 / 1000000) ≤ (441854753 / 1000000000) := by
  have h := checkLog_sound (w := (357157 / 1642843)) (n := 12)
    (lo := (13807961 / 31250000)) (hi := (441854753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 642843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 642843) = 1/(642843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13285 : Bounds (-441854753 / 1000000000) (-13807961 / 31250000) (Real.log (642843 / 1000000)) := by
  have h := reflection_log_13285_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13286_neg : (153632779 / 500000000) ≤ -Real.log (500000 / 679851) ∧
    -Real.log (500000 / 679851) ≤ (307265559 / 1000000000) := by
  have h := checkLog_sound (w := (179851 / 1179851)) (n := 12)
    (lo := (153632779 / 500000000)) (hi := (307265559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679851 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679851 / 500000) = 1/(500000 / 679851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13286 : Bounds (153632779 / 500000000) (307265559 / 1000000000) (Real.log (679851 / 500000)) := by
  have h := reflection_log_13286_neg
  have he : Real.log (679851 / 500000) = -Real.log (500000 / 679851) := by
    rw [show ((679851 / 500000) : ℝ) = ((500000 / 679851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13287_neg : (89164317 / 200000000) ≤ -Real.log (320149 / 500000) ∧
    -Real.log (320149 / 500000) ≤ (222910793 / 500000000) := by
  have h := checkLog_sound (w := (179851 / 820149)) (n := 12)
    (lo := (89164317 / 200000000)) (hi := (222910793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 320149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 320149) = 1/(320149 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13287 : Bounds (-222910793 / 500000000) (-89164317 / 200000000) (Real.log (320149 / 500000)) := by
  have h := reflection_log_13287_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13288_neg : (138556027 / 1000000000) ≤ -Real.log (217653617799 / 250000000000) ∧
    -Real.log (217653617799 / 250000000000) ≤ (34639007 / 250000000) := by
  have h := checkLog_sound (w := (32346382201 / 467653617799)) (n := 12)
    (lo := (138556027 / 1000000000)) (hi := (34639007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 217653617799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 217653617799) = 1/(217653617799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13288 : Bounds (-34639007 / 250000000) (-138556027 / 1000000000) (Real.log (217653617799 / 250000000000)) := by
  have h := reflection_log_13288_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13289_neg : (136462681 / 1000000000) ≤ -Real.log (872438877351 / 1000000000000) ∧
    -Real.log (872438877351 / 1000000000000) ≤ (68231341 / 500000000) := by
  have h := checkLog_sound (w := (127561122649 / 1872438877351)) (n := 12)
    (lo := (136462681 / 1000000000)) (hi := (68231341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 872438877351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 872438877351) = 1/(872438877351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13289 : Bounds (-68231341 / 500000000) (-136462681 / 1000000000) (Real.log (872438877351 / 1000000000000)) := by
  have h := reflection_log_13289_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13290_neg : (373623411 / 500000000) ≤ -Real.log (50000000000 / 105558977853) ∧
    -Real.log (50000000000 / 105558977853) ≤ (93405853 / 125000000) := by
  have h := checkLog_sound (w := (5558977853 / 205558977853)) (n := 12)
    (lo := (27049821 / 500000000)) (hi := (54099643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105558977853 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(105558977853 / 100000000000) = 1/(50000000000 / 105558977853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13290 : Bounds (373623411 / 500000000) (93405853 / 125000000) (Real.log (105558977853 / 50000000000)) := by
  have h := reflection_log_13290_neg
  have he : Real.log (105558977853 / 50000000000) = -Real.log (50000000000 / 105558977853) := by
    rw [show ((105558977853 / 50000000000) : ℝ) = ((50000000000 / 105558977853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13291_neg : (753087143 / 1000000000) ≤ -Real.log (500000000000 / 1061772799541) ∧
    -Real.log (500000000000 / 1061772799541) ≤ (150617429 / 200000000) := by
  have h := checkLog_sound (w := (61772799541 / 2061772799541)) (n := 12)
    (lo := (59939963 / 1000000000)) (hi := (14984991 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1061772799541 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1061772799541 / 1000000000000) = 1/(500000000000 / 1061772799541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13291 : Bounds (753087143 / 1000000000) (150617429 / 200000000) (Real.log (1061772799541 / 500000000000)) := by
  have h := reflection_log_13291_neg
  have he : Real.log (1061772799541 / 500000000000) = -Real.log (500000000000 / 1061772799541) := by
    rw [show ((1061772799541 / 500000000000) : ℝ) = ((500000000000 / 1061772799541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13292_neg : (392879669 / 250000000) ≤ -Real.log (250000000000 / 1203488372093) ∧
    -Real.log (250000000000 / 1203488372093) ≤ (1571518679 / 1000000000) := by
  have h := checkLog_sound (w := (203488372093 / 2203488372093)) (n := 12)
    (lo := (46306079 / 250000000)) (hi := (185224317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203488372093 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1203488372093 / 1000000000000) = 1/(250000000000 / 1203488372093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13292 : Bounds (392879669 / 250000000) (1571518679 / 1000000000) (Real.log (1203488372093 / 250000000000)) := by
  have h := reflection_log_13292_neg
  have he : Real.log (1203488372093 / 250000000000) = -Real.log (250000000000 / 1203488372093) := by
    rw [show ((1203488372093 / 250000000000) : ℝ) = ((250000000000 / 1203488372093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13293_neg : (1582087811 / 1000000000) ≤ -Real.log (500000000000 / 2432551319649) ∧
    -Real.log (500000000000 / 2432551319649) ≤ (791043907 / 500000000) := by
  have h := checkLog_sound (w := (432551319649 / 4432551319649)) (n := 12)
    (lo := (195793451 / 1000000000)) (hi := (48948363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2432551319649 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2432551319649 / 2000000000000) = 1/(500000000000 / 2432551319649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13293 : Bounds (1582087811 / 1000000000) (791043907 / 500000000) (Real.log (2432551319649 / 500000000000)) := by
  have h := reflection_log_13293_neg
  have he : Real.log (2432551319649 / 500000000000) = -Real.log (500000000000 / 2432551319649) := by
    rw [show ((2432551319649 / 500000000000) : ℝ) = ((500000000000 / 2432551319649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13294_neg : (7937839 / 15625000) ≤ -Real.log (500 / 831) ∧
    -Real.log (500 / 831) ≤ (508021697 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1331)) (n := 12)
    (lo := (7937839 / 15625000)) (hi := (508021697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831 / 500) = 1/(500 / 831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13294 : Bounds (7937839 / 15625000) (508021697 / 1000000000) (Real.log (831 / 500)) := by
  have h := reflection_log_13294_neg
  have he : Real.log (831 / 500) = -Real.log (500 / 831) := by
    rw [show ((831 / 500) : ℝ) = ((500 / 831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13295_neg : (542354691 / 500000000) ≤ -Real.log (169 / 500) ∧
    -Real.log (169 / 500) ≤ (135588673 / 125000000) := by
  have h := checkLog_sound (w := (81 / 419)) (n := 12)
    (lo := (195781101 / 500000000)) (hi := (391562203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 169) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 169) = 1/(169 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13295 : Bounds (-135588673 / 125000000) (-542354691 / 500000000) (Real.log (169 / 500)) := by
  have h := reflection_log_13295_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13296_neg : (33089 / 50000000) ≤ -Real.log (500000 / 500331) ∧
    -Real.log (500000 / 500331) ≤ (661781 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1000331)) (n := 12)
    (lo := (33089 / 50000000)) (hi := (661781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500331 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500331 / 500000) = 1/(500000 / 500331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13296 : Bounds (33089 / 50000000) (661781 / 1000000000) (Real.log (500331 / 500000)) := by
  have h := reflection_log_13296_neg
  have he : Real.log (500331 / 500000) = -Real.log (500000 / 500331) := by
    rw [show ((500331 / 500000) : ℝ) = ((500000 / 500331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13297_neg : (662219 / 1000000000) ≤ -Real.log (499669 / 500000) ∧
    -Real.log (499669 / 500000) ≤ (33111 / 50000000) := by
  have h := checkLog_sound (w := (331 / 999669)) (n := 12)
    (lo := (662219 / 1000000000)) (hi := (33111 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499669) = 1/(499669 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13297 : Bounds (-33111 / 50000000) (-662219 / 1000000000) (Real.log (499669 / 500000)) := by
  have h := reflection_log_13297_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13298_neg : (306830073 / 1000000000) ≤ -Real.log (100000 / 135911) ∧
    -Real.log (100000 / 135911) ≤ (153415037 / 500000000) := by
  have h := checkLog_sound (w := (35911 / 235911)) (n := 12)
    (lo := (306830073 / 1000000000)) (hi := (153415037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135911 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135911 / 100000) = 1/(100000 / 135911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13298 : Bounds (306830073 / 1000000000) (153415037 / 500000000) (Real.log (135911 / 100000)) := by
  have h := reflection_log_13298_neg
  have he : Real.log (135911 / 100000) = -Real.log (100000 / 135911) := by
    rw [show ((135911 / 100000) : ℝ) = ((100000 / 135911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13299_neg : (444897443 / 1000000000) ≤ -Real.log (64089 / 100000) ∧
    -Real.log (64089 / 100000) ≤ (111224361 / 250000000) := by
  have h := checkLog_sound (w := (35911 / 164089)) (n := 12)
    (lo := (444897443 / 1000000000)) (hi := (111224361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 64089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 64089) = 1/(64089 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13299 : Bounds (-111224361 / 250000000) (-444897443 / 1000000000) (Real.log (64089 / 100000)) := by
  have h := reflection_log_13299_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13300_neg : (77176503 / 250000000) ≤ -Real.log (500000 / 680831) ∧
    -Real.log (500000 / 680831) ≤ (308706013 / 1000000000) := by
  have h := checkLog_sound (w := (180831 / 1180831)) (n := 12)
    (lo := (77176503 / 250000000)) (hi := (308706013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680831 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680831 / 500000) = 1/(500000 / 680831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13300 : Bounds (77176503 / 250000000) (308706013 / 1000000000) (Real.log (680831 / 500000)) := by
  have h := reflection_log_13300_neg
  have he : Real.log (680831 / 500000) = -Real.log (500000 / 680831) := by
    rw [show ((680831 / 500000) : ℝ) = ((500000 / 680831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13301_neg : (89777471 / 200000000) ≤ -Real.log (319169 / 500000) ∧
    -Real.log (319169 / 500000) ≤ (112221839 / 250000000) := by
  have h := checkLog_sound (w := (180831 / 819169)) (n := 12)
    (lo := (89777471 / 200000000)) (hi := (112221839 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 319169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 319169) = 1/(319169 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13301 : Bounds (-112221839 / 250000000) (-89777471 / 200000000) (Real.log (319169 / 500000)) := by
  have h := reflection_log_13301_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13302_neg : (70090671 / 500000000) ≤ -Real.log (217300149439 / 250000000000) ∧
    -Real.log (217300149439 / 250000000000) ≤ (140181343 / 1000000000) := by
  have h := checkLog_sound (w := (32699850561 / 467300149439)) (n := 12)
    (lo := (70090671 / 500000000)) (hi := (140181343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 217300149439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 217300149439) = 1/(217300149439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13302 : Bounds (-140181343 / 1000000000) (-70090671 / 500000000) (Real.log (217300149439 / 250000000000)) := by
  have h := reflection_log_13302_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13303_neg : (138067369 / 1000000000) ≤ -Real.log (8710400079 / 10000000000) ∧
    -Real.log (8710400079 / 10000000000) ≤ (13806737 / 100000000) := by
  have h := checkLog_sound (w := (1289599921 / 18710400079)) (n := 12)
    (lo := (138067369 / 1000000000)) (hi := (13806737 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 8710400079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 8710400079) = 1/(8710400079 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13303 : Bounds (-13806737 / 100000000) (-138067369 / 1000000000) (Real.log (8710400079 / 10000000000)) := by
  have h := reflection_log_13303_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13304_neg : (187931879 / 250000000) ≤ -Real.log (500000000000 / 1060330165863) ∧
    -Real.log (500000000000 / 1060330165863) ≤ (375863759 / 500000000) := by
  have h := checkLog_sound (w := (60330165863 / 2060330165863)) (n := 12)
    (lo := (3661271 / 62500000)) (hi := (58580337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1060330165863 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1060330165863 / 1000000000000) = 1/(500000000000 / 1060330165863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13304 : Bounds (187931879 / 250000000) (375863759 / 500000000) (Real.log (1060330165863 / 500000000000)) := by
  have h := reflection_log_13304_neg
  have he : Real.log (1060330165863 / 500000000000) = -Real.log (500000000000 / 1060330165863) := by
    rw [show ((1060330165863 / 500000000000) : ℝ) = ((500000000000 / 1060330165863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13305_neg : (757593367 / 1000000000) ≤ -Real.log (500000000000 / 1066568181747) ∧
    -Real.log (500000000000 / 1066568181747) ≤ (757593369 / 1000000000) := by
  have h := checkLog_sound (w := (66568181747 / 2066568181747)) (n := 12)
    (lo := (64446187 / 1000000000)) (hi := (16111547 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1066568181747 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1066568181747 / 1000000000000) = 1/(500000000000 / 1066568181747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13305 : Bounds (757593367 / 1000000000) (757593369 / 1000000000) (Real.log (1066568181747 / 500000000000)) := by
  have h := reflection_log_13305_neg
  have he : Real.log (1066568181747 / 500000000000) = -Real.log (500000000000 / 1066568181747) := by
    rw [show ((1066568181747 / 500000000000) : ℝ) = ((500000000000 / 1066568181747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13306_neg : (1582087811 / 1000000000) ≤ -Real.log (15625000000 / 76017228739) ∧
    -Real.log (15625000000 / 76017228739) ≤ (791043907 / 500000000) := by
  have h := checkLog_sound (w := (13517228739 / 138517228739)) (n := 12)
    (lo := (195793451 / 1000000000)) (hi := (48948363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76017228739 / 62500000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(76017228739 / 62500000000) = 1/(15625000000 / 76017228739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13306 : Bounds (1582087811 / 1000000000) (791043907 / 500000000) (Real.log (76017228739 / 15625000000)) := by
  have h := reflection_log_13306_neg
  have he : Real.log (76017228739 / 15625000000) = -Real.log (15625000000 / 76017228739) := by
    rw [show ((76017228739 / 15625000000) : ℝ) = ((15625000000 / 76017228739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13307_neg : (796365539 / 500000000) ≤ -Real.log (500000000000 / 2458579881657) ∧
    -Real.log (500000000000 / 2458579881657) ≤ (1592731081 / 1000000000) := by
  have h := checkLog_sound (w := (458579881657 / 4458579881657)) (n := 12)
    (lo := (103218359 / 500000000)) (hi := (206436719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2458579881657 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2458579881657 / 2000000000000) = 1/(500000000000 / 2458579881657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13307 : Bounds (796365539 / 500000000) (1592731081 / 1000000000) (Real.log (2458579881657 / 500000000000)) := by
  have h := reflection_log_13307_neg
  have he : Real.log (2458579881657 / 500000000000) = -Real.log (500000000000 / 2458579881657) := by
    rw [show ((2458579881657 / 500000000000) : ℝ) = ((500000000000 / 2458579881657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13308_neg : (509825123 / 1000000000) ≤ -Real.log (200 / 333) ∧
    -Real.log (200 / 333) ≤ (127456281 / 250000000) := by
  have h := checkLog_sound (w := (133 / 533)) (n := 12)
    (lo := (509825123 / 1000000000)) (hi := (127456281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333 / 200) = 1/(200 / 333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13308 : Bounds (509825123 / 1000000000) (127456281 / 250000000) (Real.log (333 / 200)) := by
  have h := reflection_log_13308_neg
  have he : Real.log (333 / 200) = -Real.log (200 / 333) := by
    rw [show ((333 / 200) : ℝ) = ((200 / 333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13309_neg : (546812373 / 500000000) ≤ -Real.log (67 / 200) ∧
    -Real.log (67 / 200) ≤ (273406187 / 250000000) := by
  have h := checkLog_sound (w := (33 / 167)) (n := 12)
    (lo := (200238783 / 500000000)) (hi := (400477567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 67) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 67) = 1/(67 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13309 : Bounds (-273406187 / 250000000) (-546812373 / 500000000) (Real.log (67 / 200)) := by
  have h := reflection_log_13309_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13310_neg : (332389 / 500000000) ≤ -Real.log (200000 / 200133) ∧
    -Real.log (200000 / 200133) ≤ (664779 / 1000000000) := by
  have h := checkLog_sound (w := (133 / 400133)) (n := 12)
    (lo := (332389 / 500000000)) (hi := (664779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200133 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200133 / 200000) = 1/(200000 / 200133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13310 : Bounds (332389 / 500000000) (664779 / 1000000000) (Real.log (200133 / 200000)) := by
  have h := reflection_log_13310_neg
  have he : Real.log (200133 / 200000) = -Real.log (200000 / 200133) := by
    rw [show ((200133 / 200000) : ℝ) = ((200000 / 200133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13311_neg : (665221 / 1000000000) ≤ -Real.log (199867 / 200000) ∧
    -Real.log (199867 / 200000) ≤ (332611 / 500000000) := by
  have h := checkLog_sound (w := (133 / 399867)) (n := 12)
    (lo := (665221 / 1000000000)) (hi := (332611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199867) = 1/(199867 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13311 : Bounds (-332611 / 500000000) (-665221 / 1000000000) (Real.log (199867 / 200000)) := by
  have h := reflection_log_13311_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
