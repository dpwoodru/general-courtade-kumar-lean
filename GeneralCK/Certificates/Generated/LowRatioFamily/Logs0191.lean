import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12224_neg : (285302239 / 1000000000) ≤ -Real.log (751787 / 1000000) ∧
    -Real.log (751787 / 1000000) ≤ (1783139 / 6250000) := by
  have h := checkLog_sound (w := (248213 / 1751787)) (n := 12)
    (lo := (285302239 / 1000000000)) (hi := (1783139 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 751787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 751787) = 1/(751787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12224 : Bounds (-1783139 / 6250000) (-285302239 / 1000000000) (Real.log (751787 / 1000000)) := by
  have h := reflection_log_12224_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12225_neg : (55633241 / 250000000) ≤ -Real.log (1000000 / 1249237) ∧
    -Real.log (1000000 / 1249237) ≤ (44506593 / 200000000) := by
  have h := checkLog_sound (w := (249237 / 2249237)) (n := 12)
    (lo := (55633241 / 250000000)) (hi := (44506593 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249237 / 1000000) = 1/(1000000 / 1249237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12225 : Bounds (55633241 / 250000000) (44506593 / 200000000) (Real.log (1249237 / 1000000)) := by
  have h := reflection_log_12225_neg
  have he : Real.log (1249237 / 1000000) = -Real.log (1000000 / 1249237) := by
    rw [show ((1249237 / 1000000) : ℝ) = ((1000000 / 1249237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12226_neg : (35833157 / 125000000) ≤ -Real.log (750763 / 1000000) ∧
    -Real.log (750763 / 1000000) ≤ (286665257 / 1000000000) := by
  have h := checkLog_sound (w := (249237 / 1750763)) (n := 12)
    (lo := (35833157 / 125000000)) (hi := (286665257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 750763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 750763) = 1/(750763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12226 : Bounds (-286665257 / 1000000000) (-35833157 / 125000000) (Real.log (750763 / 1000000)) := by
  have h := reflection_log_12226_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12227_neg : (64132291 / 1000000000) ≤ -Real.log (937880917831 / 1000000000000) ∧
    -Real.log (937880917831 / 1000000000000) ≤ (16033073 / 250000000) := by
  have h := checkLog_sound (w := (62119082169 / 1937880917831)) (n := 12)
    (lo := (64132291 / 1000000000)) (hi := (16033073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 937880917831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 937880917831) = 1/(937880917831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12227 : Bounds (-16033073 / 250000000) (-64132291 / 1000000000) (Real.log (937880917831 / 1000000000000)) := by
  have h := reflection_log_12227_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12228_neg : (63589311 / 1000000000) ≤ -Real.log (938390306631 / 1000000000000) ∧
    -Real.log (938390306631 / 1000000000000) ≤ (993583 / 15625000) := by
  have h := checkLog_sound (w := (61609693369 / 1938390306631)) (n := 12)
    (lo := (63589311 / 1000000000)) (hi := (993583 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 938390306631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 938390306631) = 1/(938390306631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12228 : Bounds (-993583 / 15625000) (-63589311 / 1000000000) (Real.log (938390306631 / 1000000000000)) := by
  have h := reflection_log_12228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12229_neg : (990264 / 1953125) ≤ -Real.log (500000000000 / 830163995919) ∧
    -Real.log (500000000000 / 830163995919) ≤ (507015169 / 1000000000) := by
  have h := checkLog_sound (w := (330163995919 / 1330163995919)) (n := 12)
    (lo := (990264 / 1953125)) (hi := (507015169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((830163995919 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(830163995919 / 500000000000) = 1/(500000000000 / 830163995919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12229 : Bounds (990264 / 1953125) (507015169 / 1000000000) (Real.log (830163995919 / 500000000000)) := by
  have h := reflection_log_12229_neg
  have he : Real.log (830163995919 / 500000000000) = -Real.log (500000000000 / 830163995919) := by
    rw [show ((830163995919 / 500000000000) : ℝ) = ((500000000000 / 830163995919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12230_neg : (509198221 / 1000000000) ≤ -Real.log (500000000000 / 831978267443) ∧
    -Real.log (500000000000 / 831978267443) ≤ (254599111 / 500000000) := by
  have h := checkLog_sound (w := (331978267443 / 1331978267443)) (n := 12)
    (lo := (509198221 / 1000000000)) (hi := (254599111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831978267443 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831978267443 / 500000000000) = 1/(500000000000 / 831978267443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12230 : Bounds (509198221 / 1000000000) (254599111 / 500000000) (Real.log (831978267443 / 500000000000)) := by
  have h := reflection_log_12230_neg
  have he : Real.log (831978267443 / 500000000000) = -Real.log (500000000000 / 831978267443) := by
    rw [show ((831978267443 / 500000000000) : ℝ) = ((500000000000 / 831978267443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12231_neg : (25889983 / 25000000) ≤ -Real.log (125000000000 / 352099236641) ∧
    -Real.log (125000000000 / 352099236641) ≤ (517799661 / 500000000) := by
  have h := checkLog_sound (w := (102099236641 / 602099236641)) (n := 12)
    (lo := (17122607 / 50000000)) (hi := (342452141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352099236641 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(352099236641 / 250000000000) = 1/(125000000000 / 352099236641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12231 : Bounds (25889983 / 25000000) (517799661 / 500000000) (Real.log (352099236641 / 125000000000)) := by
  have h := reflection_log_12231_neg
  have he : Real.log (352099236641 / 125000000000) = -Real.log (125000000000 / 352099236641) := by
    rw [show ((352099236641 / 125000000000) : ℝ) = ((125000000000 / 352099236641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12232_neg : (1038186817 / 1000000000) ≤ -Real.log (250000000000 / 706022944551) ∧
    -Real.log (250000000000 / 706022944551) ≤ (1038186819 / 1000000000) := by
  have h := checkLog_sound (w := (206022944551 / 1206022944551)) (n := 12)
    (lo := (345039637 / 1000000000)) (hi := (172519819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((706022944551 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(706022944551 / 500000000000) = 1/(250000000000 / 706022944551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12232 : Bounds (1038186817 / 1000000000) (1038186819 / 1000000000) (Real.log (706022944551 / 250000000000)) := by
  have h := reflection_log_12232_neg
  have he : Real.log (706022944551 / 250000000000) = -Real.log (250000000000 / 706022944551) := by
    rw [show ((706022944551 / 250000000000) : ℝ) = ((250000000000 / 706022944551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12233_neg : (195344911 / 500000000) ≤ -Real.log (500 / 739) ∧
    -Real.log (500 / 739) ≤ (390689823 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 1239)) (n := 12)
    (lo := (195344911 / 500000000)) (hi := (390689823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739 / 500) = 1/(500 / 739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12233 : Bounds (195344911 / 500000000) (390689823 / 1000000000) (Real.log (739 / 500)) := by
  have h := reflection_log_12233_neg
  have he : Real.log (739 / 500) = -Real.log (500 / 739) := by
    rw [show ((739 / 500) : ℝ) = ((500 / 739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12234_neg : (650087691 / 1000000000) ≤ -Real.log (261 / 500) ∧
    -Real.log (261 / 500) ≤ (162521923 / 250000000) := by
  have h := checkLog_sound (w := (239 / 761)) (n := 12)
    (lo := (650087691 / 1000000000)) (hi := (162521923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 261) = 1/(261 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12234 : Bounds (-162521923 / 250000000) (-650087691 / 1000000000) (Real.log (261 / 500)) := by
  have h := reflection_log_12234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12235_neg : (95577 / 200000000) ≤ -Real.log (500000 / 500239) ∧
    -Real.log (500000 / 500239) ≤ (238943 / 500000000) := by
  have h := checkLog_sound (w := (239 / 1000239)) (n := 12)
    (lo := (95577 / 200000000)) (hi := (238943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500239 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500239 / 500000) = 1/(500000 / 500239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12235 : Bounds (95577 / 200000000) (238943 / 500000000) (Real.log (500239 / 500000)) := by
  have h := reflection_log_12235_neg
  have he : Real.log (500239 / 500000) = -Real.log (500000 / 500239) := by
    rw [show ((500239 / 500000) : ℝ) = ((500000 / 500239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12236_neg : (239057 / 500000000) ≤ -Real.log (499761 / 500000) ∧
    -Real.log (499761 / 500000) ≤ (95623 / 200000000) := by
  have h := checkLog_sound (w := (239 / 999761)) (n := 12)
    (lo := (239057 / 500000000)) (hi := (95623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499761) = 1/(499761 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12236 : Bounds (-95623 / 200000000) (-239057 / 500000000) (Real.log (499761 / 500000)) := by
  have h := reflection_log_12236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12237_neg : (55542169 / 250000000) ≤ -Real.log (500000 / 624391) ∧
    -Real.log (500000 / 624391) ≤ (222168677 / 1000000000) := by
  have h := checkLog_sound (w := (124391 / 1124391)) (n := 12)
    (lo := (55542169 / 250000000)) (hi := (222168677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624391 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624391 / 500000) = 1/(500000 / 624391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12237 : Bounds (55542169 / 250000000) (222168677 / 1000000000) (Real.log (624391 / 500000)) := by
  have h := reflection_log_12237_neg
  have he : Real.log (624391 / 500000) = -Real.log (500000 / 624391) := by
    rw [show ((624391 / 500000) : ℝ) = ((500000 / 624391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12238_neg : (286059389 / 1000000000) ≤ -Real.log (375609 / 500000) ∧
    -Real.log (375609 / 500000) ≤ (28605939 / 100000000) := by
  have h := checkLog_sound (w := (124391 / 875609)) (n := 12)
    (lo := (286059389 / 1000000000)) (hi := (28605939 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375609) = 1/(375609 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12238 : Bounds (-28605939 / 100000000) (-286059389 / 1000000000) (Real.log (375609 / 500000)) := by
  have h := reflection_log_12238_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12239_neg : (222989139 / 1000000000) ≤ -Real.log (1000000 / 1249807) ∧
    -Real.log (1000000 / 1249807) ≤ (11149457 / 50000000) := by
  have h := checkLog_sound (w := (249807 / 2249807)) (n := 12)
    (lo := (222989139 / 1000000000)) (hi := (11149457 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249807 / 1000000) = 1/(1000000 / 1249807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12239 : Bounds (222989139 / 1000000000) (11149457 / 50000000) (Real.log (1249807 / 1000000)) := by
  have h := reflection_log_12239_neg
  have he : Real.log (1249807 / 1000000) = -Real.log (1000000 / 1249807) := by
    rw [show ((1249807 / 1000000) : ℝ) = ((1000000 / 1249807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12240_neg : (71856193 / 250000000) ≤ -Real.log (750193 / 1000000) ∧
    -Real.log (750193 / 1000000) ≤ (287424773 / 1000000000) := by
  have h := checkLog_sound (w := (249807 / 1750193)) (n := 12)
    (lo := (71856193 / 250000000)) (hi := (287424773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 750193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 750193) = 1/(750193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12240 : Bounds (-287424773 / 1000000000) (-71856193 / 250000000) (Real.log (750193 / 1000000)) := by
  have h := reflection_log_12240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12241_neg : (4027227 / 62500000) ≤ -Real.log (937596462751 / 1000000000000) ∧
    -Real.log (937596462751 / 1000000000000) ≤ (64435633 / 1000000000) := by
  have h := checkLog_sound (w := (62403537249 / 1937596462751)) (n := 12)
    (lo := (4027227 / 62500000)) (hi := (64435633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 937596462751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 937596462751) = 1/(937596462751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12241 : Bounds (-64435633 / 1000000000) (-4027227 / 62500000) (Real.log (937596462751 / 1000000000000)) := by
  have h := reflection_log_12241_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12242_neg : (63890713 / 1000000000) ≤ -Real.log (234526879119 / 250000000000) ∧
    -Real.log (234526879119 / 250000000000) ≤ (31945357 / 500000000) := by
  have h := checkLog_sound (w := (15473120881 / 484526879119)) (n := 12)
    (lo := (63890713 / 1000000000)) (hi := (31945357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 234526879119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 234526879119) = 1/(234526879119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12242 : Bounds (-31945357 / 500000000) (-63890713 / 1000000000) (Real.log (234526879119 / 250000000000)) := by
  have h := reflection_log_12242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12243_neg : (101645613 / 200000000) ≤ -Real.log (500000000000 / 831171510799) ∧
    -Real.log (500000000000 / 831171510799) ≤ (254114033 / 500000000) := by
  have h := checkLog_sound (w := (331171510799 / 1331171510799)) (n := 12)
    (lo := (101645613 / 200000000)) (hi := (254114033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831171510799 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831171510799 / 500000000000) = 1/(500000000000 / 831171510799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12243 : Bounds (101645613 / 200000000) (254114033 / 500000000) (Real.log (831171510799 / 500000000000)) := by
  have h := reflection_log_12243_neg
  have he : Real.log (831171510799 / 500000000000) = -Real.log (500000000000 / 831171510799) := by
    rw [show ((831171510799 / 500000000000) : ℝ) = ((500000000000 / 831171510799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12244_neg : (510413911 / 1000000000) ≤ -Real.log (250000000000 / 416495155247) ∧
    -Real.log (250000000000 / 416495155247) ≤ (63801739 / 125000000) := by
  have h := checkLog_sound (w := (166495155247 / 666495155247)) (n := 12)
    (lo := (510413911 / 1000000000)) (hi := (63801739 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((416495155247 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(416495155247 / 250000000000) = 1/(250000000000 / 416495155247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12244 : Bounds (510413911 / 1000000000) (63801739 / 125000000) (Real.log (416495155247 / 250000000000)) := by
  have h := reflection_log_12244_neg
  have he : Real.log (416495155247 / 250000000000) = -Real.log (250000000000 / 416495155247) := by
    rw [show ((416495155247 / 250000000000) : ℝ) = ((250000000000 / 416495155247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12245_neg : (1038186817 / 1000000000) ≤ -Real.log (500000000000 / 1412045889101) ∧
    -Real.log (500000000000 / 1412045889101) ≤ (1038186819 / 1000000000) := by
  have h := checkLog_sound (w := (412045889101 / 2412045889101)) (n := 12)
    (lo := (345039637 / 1000000000)) (hi := (172519819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1412045889101 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1412045889101 / 1000000000000) = 1/(500000000000 / 1412045889101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12245 : Bounds (1038186817 / 1000000000) (1038186819 / 1000000000) (Real.log (1412045889101 / 500000000000)) := by
  have h := reflection_log_12245_neg
  have he : Real.log (1412045889101 / 500000000000) = -Real.log (500000000000 / 1412045889101) := by
    rw [show ((1412045889101 / 500000000000) : ℝ) = ((500000000000 / 1412045889101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12246_neg : (1040777513 / 1000000000) ≤ -Real.log (500000000000 / 1415708812261) ∧
    -Real.log (500000000000 / 1415708812261) ≤ (208155503 / 200000000) := by
  have h := checkLog_sound (w := (415708812261 / 2415708812261)) (n := 12)
    (lo := (347630333 / 1000000000)) (hi := (173815167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1415708812261 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1415708812261 / 1000000000000) = 1/(500000000000 / 1415708812261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12246 : Bounds (1040777513 / 1000000000) (208155503 / 200000000) (Real.log (1415708812261 / 500000000000)) := by
  have h := reflection_log_12246_neg
  have he : Real.log (1415708812261 / 500000000000) = -Real.log (500000000000 / 1415708812261) := by
    rw [show ((1415708812261 / 500000000000) : ℝ) = ((500000000000 / 1415708812261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12247_neg : (391366183 / 1000000000) ≤ -Real.log (1000 / 1479) ∧
    -Real.log (1000 / 1479) ≤ (48920773 / 125000000) := by
  have h := checkLog_sound (w := (479 / 2479)) (n := 12)
    (lo := (391366183 / 1000000000)) (hi := (48920773 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1479 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1479 / 1000) = 1/(1000 / 1479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12247 : Bounds (391366183 / 1000000000) (48920773 / 125000000) (Real.log (1479 / 1000)) := by
  have h := reflection_log_12247_neg
  have he : Real.log (1479 / 1000) = -Real.log (1000 / 1479) := by
    rw [show ((1479 / 1000) : ℝ) = ((1000 / 1479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12248_neg : (652005237 / 1000000000) ≤ -Real.log (521 / 1000) ∧
    -Real.log (521 / 1000) ≤ (326002619 / 500000000) := by
  have h := checkLog_sound (w := (479 / 1521)) (n := 12)
    (lo := (652005237 / 1000000000)) (hi := (326002619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 521) = 1/(521 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12248 : Bounds (-326002619 / 500000000) (-652005237 / 1000000000) (Real.log (521 / 1000)) := by
  have h := reflection_log_12248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12249_neg : (95777 / 200000000) ≤ -Real.log (1000000 / 1000479) ∧
    -Real.log (1000000 / 1000479) ≤ (239443 / 500000000) := by
  have h := checkLog_sound (w := (479 / 2000479)) (n := 12)
    (lo := (95777 / 200000000)) (hi := (239443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000479 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000479 / 1000000) = 1/(1000000 / 1000479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12249 : Bounds (95777 / 200000000) (239443 / 500000000) (Real.log (1000479 / 1000000)) := by
  have h := reflection_log_12249_neg
  have he : Real.log (1000479 / 1000000) = -Real.log (1000000 / 1000479) := by
    rw [show ((1000479 / 1000000) : ℝ) = ((1000000 / 1000479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12250_neg : (239557 / 500000000) ≤ -Real.log (999521 / 1000000) ∧
    -Real.log (999521 / 1000000) ≤ (95823 / 200000000) := by
  have h := checkLog_sound (w := (479 / 1999521)) (n := 12)
    (lo := (239557 / 500000000)) (hi := (95823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999521) = 1/(999521 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12250 : Bounds (-95823 / 200000000) (-239557 / 500000000) (Real.log (999521 / 1000000)) := by
  have h := reflection_log_12250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12251_neg : (27828027 / 125000000) ≤ -Real.log (1000000 / 1249351) ∧
    -Real.log (1000000 / 1249351) ≤ (222624217 / 1000000000) := by
  have h := checkLog_sound (w := (249351 / 2249351)) (n := 12)
    (lo := (27828027 / 125000000)) (hi := (222624217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249351 / 1000000) = 1/(1000000 / 1249351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12251 : Bounds (27828027 / 125000000) (222624217 / 1000000000) (Real.log (1249351 / 1000000)) := by
  have h := reflection_log_12251_neg
  have he : Real.log (1249351 / 1000000) = -Real.log (1000000 / 1249351) := by
    rw [show ((1249351 / 1000000) : ℝ) = ((1000000 / 1249351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12252_neg : (286817113 / 1000000000) ≤ -Real.log (750649 / 1000000) ∧
    -Real.log (750649 / 1000000) ≤ (143408557 / 500000000) := by
  have h := checkLog_sound (w := (249351 / 1750649)) (n := 12)
    (lo := (286817113 / 1000000000)) (hi := (143408557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 750649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 750649) = 1/(750649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12252 : Bounds (-143408557 / 500000000) (-286817113 / 1000000000) (Real.log (750649 / 1000000)) := by
  have h := reflection_log_12252_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12253_neg : (44689181 / 200000000) ≤ -Real.log (500000 / 625189) ∧
    -Real.log (500000 / 625189) ≤ (111722953 / 500000000) := by
  have h := checkLog_sound (w := (125189 / 1125189)) (n := 12)
    (lo := (44689181 / 200000000)) (hi := (111722953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625189 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625189 / 500000) = 1/(500000 / 625189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12253 : Bounds (44689181 / 200000000) (111722953 / 500000000) (Real.log (625189 / 500000)) := by
  have h := reflection_log_12253_neg
  have he : Real.log (625189 / 500000) = -Real.log (500000 / 625189) := by
    rw [show ((625189 / 500000) : ℝ) = ((500000 / 625189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12254_neg : (288186199 / 1000000000) ≤ -Real.log (374811 / 500000) ∧
    -Real.log (374811 / 500000) ≤ (1440931 / 5000000) := by
  have h := checkLog_sound (w := (125189 / 874811)) (n := 12)
    (lo := (288186199 / 1000000000)) (hi := (1440931 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 374811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 374811) = 1/(374811 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12254 : Bounds (-1440931 / 5000000) (-288186199 / 1000000000) (Real.log (374811 / 500000)) := by
  have h := reflection_log_12254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12255_neg : (64740293 / 1000000000) ≤ -Real.log (234327714279 / 250000000000) ∧
    -Real.log (234327714279 / 250000000000) ≤ (32370147 / 500000000) := by
  have h := checkLog_sound (w := (15672285721 / 484327714279)) (n := 12)
    (lo := (64740293 / 1000000000)) (hi := (32370147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 234327714279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 234327714279) = 1/(234327714279 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12255 : Bounds (-32370147 / 500000000) (-64740293 / 1000000000) (Real.log (234327714279 / 250000000000)) := by
  have h := reflection_log_12255_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12256_neg : (501507 / 7812500) ≤ -Real.log (937824078799 / 1000000000000) ∧
    -Real.log (937824078799 / 1000000000000) ≤ (64192897 / 1000000000) := by
  have h := checkLog_sound (w := (62175921201 / 1937824078799)) (n := 12)
    (lo := (501507 / 7812500)) (hi := (64192897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 937824078799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 937824078799) = 1/(937824078799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12256 : Bounds (-64192897 / 1000000000) (-501507 / 7812500) (Real.log (937824078799 / 1000000000000)) := by
  have h := reflection_log_12256_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12257_neg : (509441329 / 1000000000) ≤ -Real.log (250000000000 / 416090276547) ∧
    -Real.log (250000000000 / 416090276547) ≤ (50944133 / 100000000) := by
  have h := checkLog_sound (w := (166090276547 / 666090276547)) (n := 12)
    (lo := (509441329 / 1000000000)) (hi := (50944133 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((416090276547 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(416090276547 / 250000000000) = 1/(250000000000 / 416090276547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12257 : Bounds (509441329 / 1000000000) (50944133 / 100000000) (Real.log (416090276547 / 250000000000)) := by
  have h := reflection_log_12257_neg
  have he : Real.log (416090276547 / 250000000000) = -Real.log (250000000000 / 416090276547) := by
    rw [show ((416090276547 / 250000000000) : ℝ) = ((250000000000 / 416090276547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12258_neg : (102326421 / 200000000) ≤ -Real.log (500000000000 / 834005672193) ∧
    -Real.log (500000000000 / 834005672193) ≤ (255816053 / 500000000) := by
  have h := checkLog_sound (w := (334005672193 / 1334005672193)) (n := 12)
    (lo := (102326421 / 200000000)) (hi := (255816053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((834005672193 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(834005672193 / 500000000000) = 1/(500000000000 / 834005672193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12258 : Bounds (102326421 / 200000000) (255816053 / 500000000) (Real.log (834005672193 / 500000000000)) := by
  have h := reflection_log_12258_neg
  have he : Real.log (834005672193 / 500000000000) = -Real.log (500000000000 / 834005672193) := by
    rw [show ((834005672193 / 500000000000) : ℝ) = ((500000000000 / 834005672193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12259_neg : (1040777513 / 1000000000) ≤ -Real.log (25000000000 / 70785440613) ∧
    -Real.log (25000000000 / 70785440613) ≤ (208155503 / 200000000) := by
  have h := checkLog_sound (w := (20785440613 / 120785440613)) (n := 12)
    (lo := (347630333 / 1000000000)) (hi := (173815167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70785440613 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(70785440613 / 50000000000) = 1/(25000000000 / 70785440613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12259 : Bounds (1040777513 / 1000000000) (208155503 / 200000000) (Real.log (70785440613 / 25000000000)) := by
  have h := reflection_log_12259_neg
  have he : Real.log (70785440613 / 25000000000) = -Real.log (25000000000 / 70785440613) := by
    rw [show ((70785440613 / 25000000000) : ℝ) = ((25000000000 / 70785440613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12260_neg : (52168571 / 50000000) ≤ -Real.log (250000000000 / 709692898273) ∧
    -Real.log (250000000000 / 709692898273) ≤ (521685711 / 500000000) := by
  have h := checkLog_sound (w := (209692898273 / 1209692898273)) (n := 12)
    (lo := (4377803 / 12500000)) (hi := (350224241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709692898273 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(709692898273 / 500000000000) = 1/(250000000000 / 709692898273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12260 : Bounds (52168571 / 50000000) (521685711 / 500000000) (Real.log (709692898273 / 250000000000)) := by
  have h := reflection_log_12260_neg
  have he : Real.log (709692898273 / 250000000000) = -Real.log (250000000000 / 709692898273) := by
    rw [show ((709692898273 / 250000000000) : ℝ) = ((250000000000 / 709692898273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12261_neg : (392042087 / 1000000000) ≤ -Real.log (25 / 37) ∧
    -Real.log (25 / 37) ≤ (49005261 / 125000000) := by
  have h := checkLog_sound (w := (6 / 31)) (n := 12)
    (lo := (392042087 / 1000000000)) (hi := (49005261 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37 / 25) = 1/(25 / 37) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12261 : Bounds (392042087 / 1000000000) (49005261 / 125000000) (Real.log (37 / 25)) := by
  have h := reflection_log_12261_neg
  have he : Real.log (37 / 25) = -Real.log (25 / 37) := by
    rw [show ((37 / 25) : ℝ) = ((25 / 37) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12262_neg : (653926467 / 1000000000) ≤ -Real.log (13 / 25) ∧
    -Real.log (13 / 25) ≤ (163481617 / 250000000) := by
  have h := checkLog_sound (w := (6 / 19)) (n := 12)
    (lo := (653926467 / 1000000000)) (hi := (163481617 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 13) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 13) = 1/(13 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12262 : Bounds (-163481617 / 250000000) (-653926467 / 1000000000) (Real.log (13 / 25)) := by
  have h := reflection_log_12262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12263_neg : (119971 / 250000000) ≤ -Real.log (6250 / 6253) ∧
    -Real.log (6250 / 6253) ≤ (95977 / 200000000) := by
  have h := checkLog_sound (w := (3 / 12503)) (n := 12)
    (lo := (119971 / 250000000)) (hi := (95977 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6253 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6253 / 6250) = 1/(6250 / 6253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12263 : Bounds (119971 / 250000000) (95977 / 200000000) (Real.log (6253 / 6250)) := by
  have h := reflection_log_12263_neg
  have he : Real.log (6253 / 6250) = -Real.log (6250 / 6253) := by
    rw [show ((6253 / 6250) : ℝ) = ((6250 / 6253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12264_neg : (96023 / 200000000) ≤ -Real.log (6247 / 6250) ∧
    -Real.log (6247 / 6250) ≤ (120029 / 250000000) := by
  have h := checkLog_sound (w := (3 / 12497)) (n := 12)
    (lo := (96023 / 200000000)) (hi := (120029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 6247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 6247) = 1/(6247 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12264 : Bounds (-120029 / 250000000) (-96023 / 200000000) (Real.log (6247 / 6250)) := by
  have h := reflection_log_12264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12265_neg : (223080349 / 1000000000) ≤ -Real.log (1000000 / 1249921) ∧
    -Real.log (1000000 / 1249921) ≤ (4461607 / 20000000) := by
  have h := checkLog_sound (w := (249921 / 2249921)) (n := 12)
    (lo := (223080349 / 1000000000)) (hi := (4461607 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249921 / 1000000) = 1/(1000000 / 1249921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12265 : Bounds (223080349 / 1000000000) (4461607 / 20000000) (Real.log (1249921 / 1000000)) := by
  have h := reflection_log_12265_neg
  have he : Real.log (1249921 / 1000000) = -Real.log (1000000 / 1249921) := by
    rw [show ((1249921 / 1000000) : ℝ) = ((1000000 / 1249921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12266_neg : (35947093 / 125000000) ≤ -Real.log (750079 / 1000000) ∧
    -Real.log (750079 / 1000000) ≤ (57515349 / 200000000) := by
  have h := checkLog_sound (w := (249921 / 1750079)) (n := 12)
    (lo := (35947093 / 125000000)) (hi := (57515349 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 750079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 750079) = 1/(750079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12266 : Bounds (-57515349 / 200000000) (-35947093 / 125000000) (Real.log (750079 / 1000000)) := by
  have h := reflection_log_12266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12267_neg : (223901663 / 1000000000) ≤ -Real.log (250000 / 312737) ∧
    -Real.log (250000 / 312737) ≤ (6996927 / 31250000) := by
  have h := checkLog_sound (w := (62737 / 562737)) (n := 12)
    (lo := (223901663 / 1000000000)) (hi := (6996927 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312737 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312737 / 250000) = 1/(250000 / 312737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12267 : Bounds (223901663 / 1000000000) (6996927 / 31250000) (Real.log (312737 / 250000)) := by
  have h := reflection_log_12267_neg
  have he : Real.log (312737 / 250000) = -Real.log (250000 / 312737) := by
    rw [show ((312737 / 250000) : ℝ) = ((250000 / 312737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12268_neg : (288946871 / 1000000000) ≤ -Real.log (187263 / 250000) ∧
    -Real.log (187263 / 250000) ≤ (36118359 / 125000000) := by
  have h := checkLog_sound (w := (62737 / 437263)) (n := 12)
    (lo := (288946871 / 1000000000)) (hi := (36118359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 187263) = 1/(187263 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12268 : Bounds (-36118359 / 125000000) (-288946871 / 1000000000) (Real.log (187263 / 250000)) := by
  have h := reflection_log_12268_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12269_neg : (8130651 / 125000000) ≤ -Real.log (58564068831 / 62500000000) ∧
    -Real.log (58564068831 / 62500000000) ≤ (65045209 / 1000000000) := by
  have h := checkLog_sound (w := (3935931169 / 121064068831)) (n := 12)
    (lo := (8130651 / 125000000)) (hi := (65045209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58564068831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58564068831) = 1/(58564068831 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12269 : Bounds (-65045209 / 1000000000) (-8130651 / 125000000) (Real.log (58564068831 / 62500000000)) := by
  have h := reflection_log_12269_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12270_neg : (12899279 / 200000000) ≤ -Real.log (937539493759 / 1000000000000) ∧
    -Real.log (937539493759 / 1000000000000) ≤ (16124099 / 250000000) := by
  have h := checkLog_sound (w := (62460506241 / 1937539493759)) (n := 12)
    (lo := (12899279 / 200000000)) (hi := (16124099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 937539493759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 937539493759) = 1/(937539493759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12270 : Bounds (-16124099 / 250000000) (-12899279 / 200000000) (Real.log (937539493759 / 1000000000000)) := by
  have h := reflection_log_12270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12271_neg : (510657093 / 1000000000) ≤ -Real.log (97656250 / 162732989) ∧
    -Real.log (97656250 / 162732989) ≤ (255328547 / 500000000) := by
  have h := checkLog_sound (w := (65076739 / 260389239)) (n := 12)
    (lo := (510657093 / 1000000000)) (hi := (255328547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162732989 / 97656250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162732989 / 97656250) = 1/(97656250 / 162732989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12271 : Bounds (510657093 / 1000000000) (255328547 / 500000000) (Real.log (162732989 / 97656250)) := by
  have h := reflection_log_12271_neg
  have he : Real.log (162732989 / 97656250) = -Real.log (97656250 / 162732989) := by
    rw [show ((162732989 / 97656250) : ℝ) = ((97656250 / 162732989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12272_neg : (102569707 / 200000000) ≤ -Real.log (4000000000 / 6680166397) ∧
    -Real.log (4000000000 / 6680166397) ≤ (64106067 / 125000000) := by
  have h := checkLog_sound (w := (2680166397 / 10680166397)) (n := 12)
    (lo := (102569707 / 200000000)) (hi := (64106067 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6680166397 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6680166397 / 4000000000) = 1/(4000000000 / 6680166397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12272 : Bounds (102569707 / 200000000) (64106067 / 125000000) (Real.log (6680166397 / 4000000000)) := by
  have h := reflection_log_12272_neg
  have he : Real.log (6680166397 / 4000000000) = -Real.log (4000000000 / 6680166397) := by
    rw [show ((6680166397 / 4000000000) : ℝ) = ((4000000000 / 6680166397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12273_neg : (52168571 / 50000000) ≤ -Real.log (100000000000 / 283877159309) ∧
    -Real.log (100000000000 / 283877159309) ≤ (521685711 / 500000000) := by
  have h := checkLog_sound (w := (83877159309 / 483877159309)) (n := 12)
    (lo := (4377803 / 12500000)) (hi := (350224241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((283877159309 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(283877159309 / 200000000000) = 1/(100000000000 / 283877159309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12273 : Bounds (52168571 / 50000000) (521685711 / 500000000) (Real.log (283877159309 / 100000000000)) := by
  have h := reflection_log_12273_neg
  have he : Real.log (283877159309 / 100000000000) = -Real.log (100000000000 / 283877159309) := by
    rw [show ((283877159309 / 100000000000) : ℝ) = ((100000000000 / 283877159309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12274_neg : (522984277 / 500000000) ≤ -Real.log (500000000000 / 1423076923077) ∧
    -Real.log (500000000000 / 1423076923077) ≤ (261492139 / 250000000) := by
  have h := checkLog_sound (w := (423076923077 / 2423076923077)) (n := 12)
    (lo := (176410687 / 500000000)) (hi := (2822571 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1423076923077 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1423076923077 / 1000000000000) = 1/(500000000000 / 1423076923077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12274 : Bounds (522984277 / 500000000) (261492139 / 250000000) (Real.log (1423076923077 / 500000000000)) := by
  have h := reflection_log_12274_neg
  have he : Real.log (1423076923077 / 500000000000) = -Real.log (500000000000 / 1423076923077) := by
    rw [show ((1423076923077 / 500000000000) : ℝ) = ((500000000000 / 1423076923077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12275_neg : (78543507 / 200000000) ≤ -Real.log (1000 / 1481) ∧
    -Real.log (1000 / 1481) ≤ (12272423 / 31250000) := by
  have h := checkLog_sound (w := (481 / 2481)) (n := 12)
    (lo := (78543507 / 200000000)) (hi := (12272423 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1481 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1481 / 1000) = 1/(1000 / 1481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12275 : Bounds (78543507 / 200000000) (12272423 / 31250000) (Real.log (1481 / 1000)) := by
  have h := reflection_log_12275_neg
  have he : Real.log (1481 / 1000) = -Real.log (1000 / 1481) := by
    rw [show ((1481 / 1000) : ℝ) = ((1000 / 1481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12276_neg : (131170279 / 200000000) ≤ -Real.log (519 / 1000) ∧
    -Real.log (519 / 1000) ≤ (163962849 / 250000000) := by
  have h := checkLog_sound (w := (481 / 1519)) (n := 12)
    (lo := (131170279 / 200000000)) (hi := (163962849 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 519) = 1/(519 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12276 : Bounds (-163962849 / 250000000) (-131170279 / 200000000) (Real.log (519 / 1000)) := by
  have h := reflection_log_12276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12277_neg : (120221 / 250000000) ≤ -Real.log (1000000 / 1000481) ∧
    -Real.log (1000000 / 1000481) ≤ (96177 / 200000000) := by
  have h := checkLog_sound (w := (481 / 2000481)) (n := 12)
    (lo := (120221 / 250000000)) (hi := (96177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000481 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000481 / 1000000) = 1/(1000000 / 1000481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12277 : Bounds (120221 / 250000000) (96177 / 200000000) (Real.log (1000481 / 1000000)) := by
  have h := reflection_log_12277_neg
  have he : Real.log (1000481 / 1000000) = -Real.log (1000000 / 1000481) := by
    rw [show ((1000481 / 1000000) : ℝ) = ((1000000 / 1000481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12278_neg : (96223 / 200000000) ≤ -Real.log (999519 / 1000000) ∧
    -Real.log (999519 / 1000000) ≤ (120279 / 250000000) := by
  have h := checkLog_sound (w := (481 / 1999519)) (n := 12)
    (lo := (96223 / 200000000)) (hi := (120279 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999519) = 1/(999519 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12278 : Bounds (-120279 / 250000000) (-96223 / 200000000) (Real.log (999519 / 1000000)) := by
  have h := reflection_log_12278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12279_neg : (111767737 / 500000000) ≤ -Real.log (100000 / 125049) ∧
    -Real.log (100000 / 125049) ≤ (8941419 / 40000000) := by
  have h := checkLog_sound (w := (25049 / 225049)) (n := 12)
    (lo := (111767737 / 500000000)) (hi := (8941419 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125049 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125049 / 100000) = 1/(100000 / 125049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12279 : Bounds (111767737 / 500000000) (8941419 / 40000000) (Real.log (125049 / 100000)) := by
  have h := reflection_log_12279_neg
  have he : Real.log (125049 / 100000) = -Real.log (100000 / 125049) := by
    rw [show ((125049 / 100000) : ℝ) = ((100000 / 125049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12280_neg : (288335619 / 1000000000) ≤ -Real.log (74951 / 100000) ∧
    -Real.log (74951 / 100000) ≤ (14416781 / 50000000) := by
  have h := checkLog_sound (w := (25049 / 174951)) (n := 12)
    (lo := (288335619 / 1000000000)) (hi := (14416781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 74951) = 1/(74951 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12280 : Bounds (-14416781 / 50000000) (-288335619 / 1000000000) (Real.log (74951 / 100000)) := by
  have h := reflection_log_12280_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12281_neg : (56089703 / 250000000) ≤ -Real.log (3125 / 3911) ∧
    -Real.log (3125 / 3911) ≤ (224358813 / 1000000000) := by
  have h := checkLog_sound (w := (393 / 3518)) (n := 12)
    (lo := (56089703 / 250000000)) (hi := (224358813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3911 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3911 / 3125) = 1/(3125 / 3911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12281 : Bounds (56089703 / 250000000) (224358813 / 1000000000) (Real.log (3911 / 3125)) := by
  have h := reflection_log_12281_neg
  have he : Real.log (3911 / 3125) = -Real.log (3125 / 3911) := by
    rw [show ((3911 / 3125) : ℝ) = ((3125 / 3911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12282_neg : (57942159 / 200000000) ≤ -Real.log (2339 / 3125) ∧
    -Real.log (2339 / 3125) ≤ (72427699 / 250000000) := by
  have h := checkLog_sound (w := (393 / 2732)) (n := 12)
    (lo := (57942159 / 200000000)) (hi := (72427699 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2339) = 1/(2339 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12282 : Bounds (-72427699 / 250000000) (-57942159 / 200000000) (Real.log (2339 / 3125)) := by
  have h := reflection_log_12282_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12283_neg : (65351983 / 1000000000) ≤ -Real.log (9147829 / 9765625) ∧
    -Real.log (9147829 / 9765625) ≤ (4084499 / 62500000) := by
  have h := checkLog_sound (w := (308898 / 9456727)) (n := 12)
    (lo := (65351983 / 1000000000)) (hi := (4084499 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9147829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9147829) = 1/(9147829 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12283 : Bounds (-4084499 / 62500000) (-65351983 / 1000000000) (Real.log (9147829 / 9765625)) := by
  have h := reflection_log_12283_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12284_neg : (4050009 / 62500000) ≤ -Real.log (9372547599 / 10000000000) ∧
    -Real.log (9372547599 / 10000000000) ≤ (12960029 / 200000000) := by
  have h := checkLog_sound (w := (627452401 / 19372547599)) (n := 12)
    (lo := (4050009 / 62500000)) (hi := (12960029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9372547599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9372547599) = 1/(9372547599 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12284 : Bounds (-12960029 / 200000000) (-4050009 / 62500000) (Real.log (9372547599 / 10000000000)) := by
  have h := reflection_log_12284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12285_neg : (511871093 / 1000000000) ≤ -Real.log (250000000000 / 417102506971) ∧
    -Real.log (250000000000 / 417102506971) ≤ (255935547 / 500000000) := by
  have h := checkLog_sound (w := (167102506971 / 667102506971)) (n := 12)
    (lo := (511871093 / 1000000000)) (hi := (255935547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417102506971 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417102506971 / 250000000000) = 1/(250000000000 / 417102506971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12285 : Bounds (511871093 / 1000000000) (255935547 / 500000000) (Real.log (417102506971 / 250000000000)) := by
  have h := reflection_log_12285_neg
  have he : Real.log (417102506971 / 250000000000) = -Real.log (250000000000 / 417102506971) := by
    rw [show ((417102506971 / 250000000000) : ℝ) = ((250000000000 / 417102506971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12286_neg : (64258701 / 125000000) ≤ -Real.log (500000000000 / 836041043181) ∧
    -Real.log (500000000000 / 836041043181) ≤ (514069609 / 1000000000) := by
  have h := checkLog_sound (w := (336041043181 / 1336041043181)) (n := 12)
    (lo := (64258701 / 125000000)) (hi := (514069609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((836041043181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(836041043181 / 500000000000) = 1/(500000000000 / 836041043181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12286 : Bounds (64258701 / 125000000) (514069609 / 1000000000) (Real.log (836041043181 / 500000000000)) := by
  have h := reflection_log_12286_neg
  have he : Real.log (836041043181 / 500000000000) = -Real.log (500000000000 / 836041043181) := by
    rw [show ((836041043181 / 500000000000) : ℝ) = ((500000000000 / 836041043181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12287_neg : (522984277 / 500000000) ≤ -Real.log (125000000000 / 355769230769) ∧
    -Real.log (125000000000 / 355769230769) ≤ (261492139 / 250000000) := by
  have h := checkLog_sound (w := (105769230769 / 605769230769)) (n := 12)
    (lo := (176410687 / 500000000)) (hi := (2822571 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355769230769 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(355769230769 / 250000000000) = 1/(125000000000 / 355769230769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12287 : Bounds (522984277 / 500000000) (261492139 / 250000000) (Real.log (355769230769 / 125000000000)) := by
  have h := reflection_log_12287_neg
  have he : Real.log (355769230769 / 125000000000) = -Real.log (125000000000 / 355769230769) := by
    rw [show ((355769230769 / 125000000000) : ℝ) = ((125000000000 / 355769230769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
