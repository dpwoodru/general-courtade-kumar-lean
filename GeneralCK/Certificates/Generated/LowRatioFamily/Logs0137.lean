import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8768_neg : (270940763 / 500000000) ≤ -Real.log (100000000000 / 171923861319) ∧
    -Real.log (100000000000 / 171923861319) ≤ (541881527 / 1000000000) := by
  have h := checkLog_sound (w := (71923861319 / 271923861319)) (n := 12)
    (lo := (270940763 / 500000000)) (hi := (541881527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171923861319 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171923861319 / 100000000000) = 1/(100000000000 / 171923861319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8768 : Bounds (270940763 / 500000000) (541881527 / 1000000000) (Real.log (171923861319 / 100000000000)) := by
  have h := reflection_log_8768_neg
  have he : Real.log (171923861319 / 100000000000) = -Real.log (100000000000 / 171923861319) := by
    rw [show ((171923861319 / 100000000000) : ℝ) = ((100000000000 / 171923861319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8769_neg : (117536061 / 500000000) ≤ -Real.log (200 / 253) ∧
    -Real.log (200 / 253) ≤ (235072123 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 453)) (n := 12)
    (lo := (117536061 / 500000000)) (hi := (235072123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((253 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(253 / 200) = 1/(200 / 253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8769 : Bounds (117536061 / 500000000) (235072123 / 1000000000) (Real.log (253 / 200)) := by
  have h := reflection_log_8769_neg
  have he : Real.log (253 / 200) = -Real.log (200 / 253) := by
    rw [show ((253 / 200) : ℝ) = ((200 / 253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8770_neg : (307884779 / 1000000000) ≤ -Real.log (147 / 200) ∧
    -Real.log (147 / 200) ≤ (15394239 / 50000000) := by
  have h := checkLog_sound (w := (53 / 347)) (n := 12)
    (lo := (307884779 / 1000000000)) (hi := (15394239 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 147) = 1/(147 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8770 : Bounds (-15394239 / 50000000) (-307884779 / 1000000000) (Real.log (147 / 200)) := by
  have h := reflection_log_8770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8771_neg : (66241 / 250000000) ≤ -Real.log (200000 / 200053) ∧
    -Real.log (200000 / 200053) ≤ (52993 / 200000000) := by
  have h := checkLog_sound (w := (53 / 400053)) (n := 12)
    (lo := (66241 / 250000000)) (hi := (52993 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200053 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200053 / 200000) = 1/(200000 / 200053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8771 : Bounds (66241 / 250000000) (52993 / 200000000) (Real.log (200053 / 200000)) := by
  have h := reflection_log_8771_neg
  have he : Real.log (200053 / 200000) = -Real.log (200000 / 200053) := by
    rw [show ((200053 / 200000) : ℝ) = ((200000 / 200053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8772_neg : (53007 / 200000000) ≤ -Real.log (199947 / 200000) ∧
    -Real.log (199947 / 200000) ≤ (66259 / 250000000) := by
  have h := checkLog_sound (w := (53 / 399947)) (n := 12)
    (lo := (53007 / 200000000)) (hi := (66259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199947) = 1/(199947 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8772 : Bounds (-66259 / 250000000) (-53007 / 200000000) (Real.log (199947 / 200000)) := by
  have h := reflection_log_8772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8773_neg : (31398777 / 250000000) ≤ -Real.log (1000000 / 1133823) ∧
    -Real.log (1000000 / 1133823) ≤ (125595109 / 1000000000) := by
  have h := checkLog_sound (w := (133823 / 2133823)) (n := 12)
    (lo := (31398777 / 250000000)) (hi := (125595109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1133823 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1133823 / 1000000) = 1/(1000000 / 1133823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8773 : Bounds (31398777 / 250000000) (125595109 / 1000000000) (Real.log (1133823 / 1000000)) := by
  have h := reflection_log_8773_neg
  have he : Real.log (1133823 / 1000000) = -Real.log (1000000 / 1133823) := by
    rw [show ((1133823 / 1000000) : ℝ) = ((1000000 / 1133823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8774_neg : (143666003 / 1000000000) ≤ -Real.log (866177 / 1000000) ∧
    -Real.log (866177 / 1000000) ≤ (35916501 / 250000000) := by
  have h := checkLog_sound (w := (133823 / 1866177)) (n := 12)
    (lo := (143666003 / 1000000000)) (hi := (35916501 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 866177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 866177) = 1/(866177 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8774 : Bounds (-35916501 / 250000000) (-143666003 / 1000000000) (Real.log (866177 / 1000000)) := by
  have h := reflection_log_8774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8775_neg : (126055391 / 1000000000) ≤ -Real.log (200000 / 226869) ∧
    -Real.log (200000 / 226869) ≤ (3939231 / 31250000) := by
  have h := checkLog_sound (w := (26869 / 426869)) (n := 12)
    (lo := (126055391 / 1000000000)) (hi := (3939231 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226869 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226869 / 200000) = 1/(200000 / 226869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8775 : Bounds (126055391 / 1000000000) (3939231 / 31250000) (Real.log (226869 / 200000)) := by
  have h := reflection_log_8775_neg
  have he : Real.log (226869 / 200000) = -Real.log (200000 / 226869) := by
    rw [show ((226869 / 200000) : ℝ) = ((200000 / 226869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8776_neg : (144268833 / 1000000000) ≤ -Real.log (173131 / 200000) ∧
    -Real.log (173131 / 200000) ≤ (72134417 / 500000000) := by
  have h := checkLog_sound (w := (26869 / 373131)) (n := 12)
    (lo := (144268833 / 1000000000)) (hi := (72134417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173131) = 1/(173131 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8776 : Bounds (-72134417 / 500000000) (-144268833 / 1000000000) (Real.log (173131 / 200000)) := by
  have h := reflection_log_8776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8777_neg : (18213441 / 1000000000) ≤ -Real.log (39278056839 / 40000000000) ∧
    -Real.log (39278056839 / 40000000000) ≤ (9106721 / 500000000) := by
  have h := checkLog_sound (w := (721943161 / 79278056839)) (n := 12)
    (lo := (18213441 / 1000000000)) (hi := (9106721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39278056839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39278056839) = 1/(39278056839 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8777 : Bounds (-9106721 / 500000000) (-18213441 / 1000000000) (Real.log (39278056839 / 40000000000)) := by
  have h := reflection_log_8777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8778_neg : (9035447 / 500000000) ≤ -Real.log (982091404671 / 1000000000000) ∧
    -Real.log (982091404671 / 1000000000000) ≤ (3614179 / 200000000) := by
  have h := checkLog_sound (w := (17908595329 / 1982091404671)) (n := 12)
    (lo := (9035447 / 500000000)) (hi := (3614179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982091404671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982091404671) = 1/(982091404671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8778 : Bounds (-3614179 / 200000000) (-9035447 / 500000000) (Real.log (982091404671 / 1000000000000)) := by
  have h := reflection_log_8778_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8779_neg : (269261111 / 1000000000) ≤ -Real.log (500000000000 / 654498445467) ∧
    -Real.log (500000000000 / 654498445467) ≤ (33657639 / 125000000) := by
  have h := checkLog_sound (w := (154498445467 / 1154498445467)) (n := 12)
    (lo := (269261111 / 1000000000)) (hi := (33657639 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((654498445467 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(654498445467 / 500000000000) = 1/(500000000000 / 654498445467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8779 : Bounds (269261111 / 1000000000) (33657639 / 125000000) (Real.log (654498445467 / 500000000000)) := by
  have h := reflection_log_8779_neg
  have he : Real.log (654498445467 / 500000000000) = -Real.log (500000000000 / 654498445467) := by
    rw [show ((654498445467 / 500000000000) : ℝ) = ((500000000000 / 654498445467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8780_neg : (10812969 / 40000000) ≤ -Real.log (250000000000 / 327597310707) ∧
    -Real.log (250000000000 / 327597310707) ≤ (135162113 / 500000000) := by
  have h := checkLog_sound (w := (77597310707 / 577597310707)) (n := 12)
    (lo := (10812969 / 40000000)) (hi := (135162113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327597310707 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327597310707 / 250000000000) = 1/(250000000000 / 327597310707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8780 : Bounds (10812969 / 40000000) (135162113 / 500000000) (Real.log (327597310707 / 250000000000)) := by
  have h := reflection_log_8780_neg
  have he : Real.log (327597310707 / 250000000000) = -Real.log (250000000000 / 327597310707) := by
    rw [show ((327597310707 / 250000000000) : ℝ) = ((250000000000 / 327597310707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8781_neg : (270940763 / 500000000) ≤ -Real.log (250000000000 / 429809653297) ∧
    -Real.log (250000000000 / 429809653297) ≤ (541881527 / 1000000000) := by
  have h := checkLog_sound (w := (179809653297 / 679809653297)) (n := 12)
    (lo := (270940763 / 500000000)) (hi := (541881527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429809653297 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(429809653297 / 250000000000) = 1/(250000000000 / 429809653297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8781 : Bounds (270940763 / 500000000) (541881527 / 1000000000) (Real.log (429809653297 / 250000000000)) := by
  have h := reflection_log_8781_neg
  have he : Real.log (429809653297 / 250000000000) = -Real.log (250000000000 / 429809653297) := by
    rw [show ((429809653297 / 250000000000) : ℝ) = ((250000000000 / 429809653297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8782_neg : (542956901 / 1000000000) ≤ -Real.log (62500000000 / 107568027211) ∧
    -Real.log (62500000000 / 107568027211) ≤ (271478451 / 500000000) := by
  have h := checkLog_sound (w := (45068027211 / 170068027211)) (n := 12)
    (lo := (542956901 / 1000000000)) (hi := (271478451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107568027211 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107568027211 / 62500000000) = 1/(62500000000 / 107568027211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8782 : Bounds (542956901 / 1000000000) (271478451 / 500000000) (Real.log (107568027211 / 62500000000)) := by
  have h := reflection_log_8782_neg
  have he : Real.log (107568027211 / 62500000000) = -Real.log (62500000000 / 107568027211) := by
    rw [show ((107568027211 / 62500000000) : ℝ) = ((62500000000 / 107568027211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8783_neg : (235467301 / 1000000000) ≤ -Real.log (2000 / 2531) ∧
    -Real.log (2000 / 2531) ≤ (117733651 / 500000000) := by
  have h := checkLog_sound (w := (531 / 4531)) (n := 12)
    (lo := (235467301 / 1000000000)) (hi := (117733651 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2531 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2531 / 2000) = 1/(2000 / 2531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8783 : Bounds (235467301 / 1000000000) (117733651 / 500000000) (Real.log (2531 / 2000)) := by
  have h := reflection_log_8783_neg
  have he : Real.log (2531 / 2000) = -Real.log (2000 / 2531) := by
    rw [show ((2531 / 2000) : ℝ) = ((2000 / 2531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8784_neg : (308565283 / 1000000000) ≤ -Real.log (1469 / 2000) ∧
    -Real.log (1469 / 2000) ≤ (77141321 / 250000000) := by
  have h := checkLog_sound (w := (531 / 3469)) (n := 12)
    (lo := (308565283 / 1000000000)) (hi := (77141321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1469) = 1/(1469 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8784 : Bounds (-77141321 / 250000000) (-308565283 / 1000000000) (Real.log (1469 / 2000)) := by
  have h := reflection_log_8784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8785_neg : (33183 / 125000000) ≤ -Real.log (2000000 / 2000531) ∧
    -Real.log (2000000 / 2000531) ≤ (53093 / 200000000) := by
  have h := checkLog_sound (w := (531 / 4000531)) (n := 12)
    (lo := (33183 / 125000000)) (hi := (53093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000531 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000531 / 2000000) = 1/(2000000 / 2000531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8785 : Bounds (33183 / 125000000) (53093 / 200000000) (Real.log (2000531 / 2000000)) := by
  have h := reflection_log_8785_neg
  have he : Real.log (2000531 / 2000000) = -Real.log (2000000 / 2000531) := by
    rw [show ((2000531 / 2000000) : ℝ) = ((2000000 / 2000531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8786_neg : (53107 / 200000000) ≤ -Real.log (1999469 / 2000000) ∧
    -Real.log (1999469 / 2000000) ≤ (4149 / 15625000) := by
  have h := checkLog_sound (w := (531 / 3999469)) (n := 12)
    (lo := (53107 / 200000000)) (hi := (4149 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999469) = 1/(1999469 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8786 : Bounds (-4149 / 15625000) (-53107 / 200000000) (Real.log (1999469 / 2000000)) := by
  have h := reflection_log_8786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8787_neg : (125823513 / 1000000000) ≤ -Real.log (500000 / 567041) ∧
    -Real.log (500000 / 567041) ≤ (62911757 / 500000000) := by
  have h := checkLog_sound (w := (67041 / 1067041)) (n := 12)
    (lo := (125823513 / 1000000000)) (hi := (62911757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567041 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(567041 / 500000) = 1/(500000 / 567041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8787 : Bounds (125823513 / 1000000000) (62911757 / 500000000) (Real.log (567041 / 500000)) := by
  have h := reflection_log_8787_neg
  have he : Real.log (567041 / 500000) = -Real.log (500000 / 567041) := by
    rw [show ((567041 / 500000) : ℝ) = ((500000 / 567041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8788_neg : (143965063 / 1000000000) ≤ -Real.log (432959 / 500000) ∧
    -Real.log (432959 / 500000) ≤ (17995633 / 125000000) := by
  have h := checkLog_sound (w := (67041 / 932959)) (n := 12)
    (lo := (143965063 / 1000000000)) (hi := (17995633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 432959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 432959) = 1/(432959 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8788 : Bounds (-17995633 / 125000000) (-143965063 / 1000000000) (Real.log (432959 / 500000)) := by
  have h := reflection_log_8788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8789_neg : (31571143 / 250000000) ≤ -Real.log (200000 / 226921) ∧
    -Real.log (200000 / 226921) ≤ (126284573 / 1000000000) := by
  have h := checkLog_sound (w := (26921 / 426921)) (n := 12)
    (lo := (31571143 / 250000000)) (hi := (126284573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226921 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226921 / 200000) = 1/(200000 / 226921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8789 : Bounds (31571143 / 250000000) (126284573 / 1000000000) (Real.log (226921 / 200000)) := by
  have h := reflection_log_8789_neg
  have he : Real.log (226921 / 200000) = -Real.log (200000 / 226921) := by
    rw [show ((226921 / 200000) : ℝ) = ((200000 / 226921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8790_neg : (36142307 / 250000000) ≤ -Real.log (173079 / 200000) ∧
    -Real.log (173079 / 200000) ≤ (144569229 / 1000000000) := by
  have h := checkLog_sound (w := (26921 / 373079)) (n := 12)
    (lo := (36142307 / 250000000)) (hi := (144569229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173079) = 1/(173079 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8790 : Bounds (-144569229 / 1000000000) (-36142307 / 250000000) (Real.log (173079 / 200000)) := by
  have h := reflection_log_8790_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8791_neg : (1142791 / 62500000) ≤ -Real.log (39275259759 / 40000000000) ∧
    -Real.log (39275259759 / 40000000000) ≤ (18284657 / 1000000000) := by
  have h := checkLog_sound (w := (724740241 / 79275259759)) (n := 12)
    (lo := (1142791 / 62500000)) (hi := (18284657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39275259759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39275259759) = 1/(39275259759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8791 : Bounds (-18284657 / 1000000000) (-1142791 / 62500000) (Real.log (39275259759 / 40000000000)) := by
  have h := reflection_log_8791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8792_neg : (362831 / 20000000) ≤ -Real.log (245505504319 / 250000000000) ∧
    -Real.log (245505504319 / 250000000000) ≤ (18141551 / 1000000000) := by
  have h := checkLog_sound (w := (4494495681 / 495505504319)) (n := 12)
    (lo := (362831 / 20000000)) (hi := (18141551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245505504319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245505504319) = 1/(245505504319 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8792 : Bounds (-18141551 / 1000000000) (-362831 / 20000000) (Real.log (245505504319 / 250000000000)) := by
  have h := reflection_log_8792_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8793_neg : (8430893 / 31250000) ≤ -Real.log (500000000000 / 654843761187) ∧
    -Real.log (500000000000 / 654843761187) ≤ (269788577 / 1000000000) := by
  have h := checkLog_sound (w := (154843761187 / 1154843761187)) (n := 12)
    (lo := (8430893 / 31250000)) (hi := (269788577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((654843761187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(654843761187 / 500000000000) = 1/(500000000000 / 654843761187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8793 : Bounds (8430893 / 31250000) (269788577 / 1000000000) (Real.log (654843761187 / 500000000000)) := by
  have h := reflection_log_8793_neg
  have he : Real.log (654843761187 / 500000000000) = -Real.log (500000000000 / 654843761187) := by
    rw [show ((654843761187 / 500000000000) : ℝ) = ((500000000000 / 654843761187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8794_neg : (270853801 / 1000000000) ≤ -Real.log (15625000000 / 20485677783) ∧
    -Real.log (15625000000 / 20485677783) ≤ (135426901 / 500000000) := by
  have h := checkLog_sound (w := (4860677783 / 36110677783)) (n := 12)
    (lo := (270853801 / 1000000000)) (hi := (135426901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20485677783 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20485677783 / 15625000000) = 1/(15625000000 / 20485677783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8794 : Bounds (270853801 / 1000000000) (135426901 / 500000000) (Real.log (20485677783 / 15625000000)) := by
  have h := reflection_log_8794_neg
  have he : Real.log (20485677783 / 15625000000) = -Real.log (15625000000 / 20485677783) := by
    rw [show ((20485677783 / 15625000000) : ℝ) = ((15625000000 / 20485677783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8795_neg : (542956901 / 1000000000) ≤ -Real.log (500000000000 / 860544217687) ∧
    -Real.log (500000000000 / 860544217687) ≤ (271478451 / 500000000) := by
  have h := checkLog_sound (w := (360544217687 / 1360544217687)) (n := 12)
    (lo := (542956901 / 1000000000)) (hi := (271478451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((860544217687 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(860544217687 / 500000000000) = 1/(500000000000 / 860544217687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8795 : Bounds (542956901 / 1000000000) (271478451 / 500000000) (Real.log (860544217687 / 500000000000)) := by
  have h := reflection_log_8795_neg
  have he : Real.log (860544217687 / 500000000000) = -Real.log (500000000000 / 860544217687) := by
    rw [show ((860544217687 / 500000000000) : ℝ) = ((500000000000 / 860544217687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8796_neg : (68004073 / 125000000) ≤ -Real.log (25000000000 / 43073519401) ∧
    -Real.log (25000000000 / 43073519401) ≤ (108806517 / 200000000) := by
  have h := checkLog_sound (w := (18073519401 / 68073519401)) (n := 12)
    (lo := (68004073 / 125000000)) (hi := (108806517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43073519401 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43073519401 / 25000000000) = 1/(25000000000 / 43073519401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8796 : Bounds (68004073 / 125000000) (108806517 / 200000000) (Real.log (43073519401 / 25000000000)) := by
  have h := reflection_log_8796_neg
  have he : Real.log (43073519401 / 25000000000) = -Real.log (25000000000 / 43073519401) := by
    rw [show ((43073519401 / 25000000000) : ℝ) = ((25000000000 / 43073519401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8797_neg : (235862323 / 1000000000) ≤ -Real.log (500 / 633) ∧
    -Real.log (500 / 633) ≤ (58965581 / 250000000) := by
  have h := checkLog_sound (w := (133 / 1133)) (n := 12)
    (lo := (235862323 / 1000000000)) (hi := (58965581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633 / 500) = 1/(500 / 633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8797 : Bounds (235862323 / 1000000000) (58965581 / 250000000) (Real.log (633 / 500)) := by
  have h := reflection_log_8797_neg
  have he : Real.log (633 / 500) = -Real.log (500 / 633) := by
    rw [show ((633 / 500) : ℝ) = ((500 / 633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8798_neg : (247397 / 800000) ≤ -Real.log (367 / 500) ∧
    -Real.log (367 / 500) ≤ (309246251 / 1000000000) := by
  have h := checkLog_sound (w := (133 / 867)) (n := 12)
    (lo := (247397 / 800000)) (hi := (309246251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 367) = 1/(367 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8798 : Bounds (-309246251 / 1000000000) (-247397 / 800000) (Real.log (367 / 500)) := by
  have h := reflection_log_8798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8799_neg : (66491 / 250000000) ≤ -Real.log (500000 / 500133) ∧
    -Real.log (500000 / 500133) ≤ (53193 / 200000000) := by
  have h := checkLog_sound (w := (133 / 1000133)) (n := 12)
    (lo := (66491 / 250000000)) (hi := (53193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500133 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500133 / 500000) = 1/(500000 / 500133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8799 : Bounds (66491 / 250000000) (53193 / 200000000) (Real.log (500133 / 500000)) := by
  have h := reflection_log_8799_neg
  have he : Real.log (500133 / 500000) = -Real.log (500000 / 500133) := by
    rw [show ((500133 / 500000) : ℝ) = ((500000 / 500133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8800_neg : (53207 / 200000000) ≤ -Real.log (499867 / 500000) ∧
    -Real.log (499867 / 500000) ≤ (66509 / 250000000) := by
  have h := checkLog_sound (w := (133 / 999867)) (n := 12)
    (lo := (53207 / 200000000)) (hi := (66509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499867) = 1/(499867 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8800 : Bounds (-66509 / 250000000) (-53207 / 200000000) (Real.log (499867 / 500000)) := by
  have h := reflection_log_8800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8801_neg : (126052747 / 1000000000) ≤ -Real.log (500000 / 567171) ∧
    -Real.log (500000 / 567171) ≤ (31513187 / 250000000) := by
  have h := checkLog_sound (w := (67171 / 1067171)) (n := 12)
    (lo := (126052747 / 1000000000)) (hi := (31513187 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567171 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(567171 / 500000) = 1/(500000 / 567171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8801 : Bounds (126052747 / 1000000000) (31513187 / 250000000) (Real.log (567171 / 500000)) := by
  have h := reflection_log_8801_neg
  have he : Real.log (567171 / 500000) = -Real.log (500000 / 567171) := by
    rw [show ((567171 / 500000) : ℝ) = ((500000 / 567171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8802_neg : (144265367 / 1000000000) ≤ -Real.log (432829 / 500000) ∧
    -Real.log (432829 / 500000) ≤ (18033171 / 125000000) := by
  have h := checkLog_sound (w := (67171 / 932829)) (n := 12)
    (lo := (144265367 / 1000000000)) (hi := (18033171 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 432829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 432829) = 1/(432829 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8802 : Bounds (-18033171 / 125000000) (-144265367 / 1000000000) (Real.log (432829 / 500000)) := by
  have h := reflection_log_8802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8803_neg : (126513701 / 1000000000) ≤ -Real.log (200000 / 226973) ∧
    -Real.log (200000 / 226973) ≤ (63256851 / 500000000) := by
  have h := checkLog_sound (w := (26973 / 426973)) (n := 12)
    (lo := (126513701 / 1000000000)) (hi := (63256851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226973 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226973 / 200000) = 1/(200000 / 226973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8803 : Bounds (126513701 / 1000000000) (63256851 / 500000000) (Real.log (226973 / 200000)) := by
  have h := reflection_log_8803_neg
  have he : Real.log (226973 / 200000) = -Real.log (200000 / 226973) := by
    rw [show ((226973 / 200000) : ℝ) = ((200000 / 226973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8804_neg : (72434857 / 500000000) ≤ -Real.log (173027 / 200000) ∧
    -Real.log (173027 / 200000) ≤ (28973943 / 200000000) := by
  have h := checkLog_sound (w := (26973 / 373027)) (n := 12)
    (lo := (72434857 / 500000000)) (hi := (28973943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173027) = 1/(173027 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8804 : Bounds (-28973943 / 200000000) (-72434857 / 500000000) (Real.log (173027 / 200000)) := by
  have h := reflection_log_8804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8805_neg : (18356013 / 1000000000) ≤ -Real.log (39272457271 / 40000000000) ∧
    -Real.log (39272457271 / 40000000000) ≤ (9178007 / 500000000) := by
  have h := checkLog_sound (w := (727542729 / 79272457271)) (n := 12)
    (lo := (18356013 / 1000000000)) (hi := (9178007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39272457271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39272457271) = 1/(39272457271 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8805 : Bounds (-9178007 / 500000000) (-18356013 / 1000000000) (Real.log (39272457271 / 40000000000)) := by
  have h := reflection_log_8805_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8806_neg : (910631 / 50000000) ≤ -Real.log (245488056759 / 250000000000) ∧
    -Real.log (245488056759 / 250000000000) ≤ (18212621 / 1000000000) := by
  have h := checkLog_sound (w := (4511943241 / 495488056759)) (n := 12)
    (lo := (910631 / 50000000)) (hi := (18212621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245488056759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245488056759) = 1/(245488056759 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8806 : Bounds (-18212621 / 1000000000) (-910631 / 50000000) (Real.log (245488056759 / 250000000000)) := by
  have h := reflection_log_8806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8807_neg : (135159057 / 500000000) ≤ -Real.log (500000000000 / 655190618003) ∧
    -Real.log (500000000000 / 655190618003) ≤ (54063623 / 200000000) := by
  have h := checkLog_sound (w := (155190618003 / 1155190618003)) (n := 12)
    (lo := (135159057 / 500000000)) (hi := (54063623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655190618003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655190618003 / 500000000000) = 1/(500000000000 / 655190618003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8807 : Bounds (135159057 / 500000000) (54063623 / 200000000) (Real.log (655190618003 / 500000000000)) := by
  have h := reflection_log_8807_neg
  have he : Real.log (655190618003 / 500000000000) = -Real.log (500000000000 / 655190618003) := by
    rw [show ((655190618003 / 500000000000) : ℝ) = ((500000000000 / 655190618003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8808_neg : (54276683 / 200000000) ≤ -Real.log (250000000000 / 327944482653) ∧
    -Real.log (250000000000 / 327944482653) ≤ (33922927 / 125000000) := by
  have h := checkLog_sound (w := (77944482653 / 577944482653)) (n := 12)
    (lo := (54276683 / 200000000)) (hi := (33922927 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327944482653 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327944482653 / 250000000000) = 1/(250000000000 / 327944482653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8808 : Bounds (54276683 / 200000000) (33922927 / 125000000) (Real.log (327944482653 / 250000000000)) := by
  have h := reflection_log_8808_neg
  have he : Real.log (327944482653 / 250000000000) = -Real.log (250000000000 / 327944482653) := by
    rw [show ((327944482653 / 250000000000) : ℝ) = ((250000000000 / 327944482653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8809_neg : (68004073 / 125000000) ≤ -Real.log (500000000000 / 861470388019) ∧
    -Real.log (500000000000 / 861470388019) ≤ (108806517 / 200000000) := by
  have h := checkLog_sound (w := (361470388019 / 1361470388019)) (n := 12)
    (lo := (68004073 / 125000000)) (hi := (108806517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((861470388019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(861470388019 / 500000000000) = 1/(500000000000 / 861470388019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8809 : Bounds (68004073 / 125000000) (108806517 / 200000000) (Real.log (861470388019 / 500000000000)) := by
  have h := reflection_log_8809_neg
  have he : Real.log (861470388019 / 500000000000) = -Real.log (500000000000 / 861470388019) := by
    rw [show ((861470388019 / 500000000000) : ℝ) = ((500000000000 / 861470388019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8810_neg : (272554287 / 500000000) ≤ -Real.log (125000000000 / 215599455041) ∧
    -Real.log (125000000000 / 215599455041) ≤ (21804343 / 40000000) := by
  have h := checkLog_sound (w := (90599455041 / 340599455041)) (n := 12)
    (lo := (272554287 / 500000000)) (hi := (21804343 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215599455041 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215599455041 / 125000000000) = 1/(125000000000 / 215599455041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8810 : Bounds (272554287 / 500000000) (21804343 / 40000000) (Real.log (215599455041 / 125000000000)) := by
  have h := reflection_log_8810_neg
  have he : Real.log (215599455041 / 125000000000) = -Real.log (125000000000 / 215599455041) := by
    rw [show ((215599455041 / 125000000000) : ℝ) = ((125000000000 / 215599455041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8811_neg : (23625719 / 100000000) ≤ -Real.log (2000 / 2533) ∧
    -Real.log (2000 / 2533) ≤ (236257191 / 1000000000) := by
  have h := checkLog_sound (w := (533 / 4533)) (n := 12)
    (lo := (23625719 / 100000000)) (hi := (236257191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2533 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2533 / 2000) = 1/(2000 / 2533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8811 : Bounds (23625719 / 100000000) (236257191 / 1000000000) (Real.log (2533 / 2000)) := by
  have h := reflection_log_8811_neg
  have he : Real.log (2533 / 2000) = -Real.log (2000 / 2533) := by
    rw [show ((2533 / 2000) : ℝ) = ((2000 / 2533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8812_neg : (309927681 / 1000000000) ≤ -Real.log (1467 / 2000) ∧
    -Real.log (1467 / 2000) ≤ (154963841 / 500000000) := by
  have h := checkLog_sound (w := (533 / 3467)) (n := 12)
    (lo := (309927681 / 1000000000)) (hi := (154963841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1467) = 1/(1467 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8812 : Bounds (-154963841 / 500000000) (-309927681 / 1000000000) (Real.log (1467 / 2000)) := by
  have h := reflection_log_8812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8813_neg : (8327 / 31250000) ≤ -Real.log (2000000 / 2000533) ∧
    -Real.log (2000000 / 2000533) ≤ (53293 / 200000000) := by
  have h := checkLog_sound (w := (533 / 4000533)) (n := 12)
    (lo := (8327 / 31250000)) (hi := (53293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000533 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000533 / 2000000) = 1/(2000000 / 2000533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8813 : Bounds (8327 / 31250000) (53293 / 200000000) (Real.log (2000533 / 2000000)) := by
  have h := reflection_log_8813_neg
  have he : Real.log (2000533 / 2000000) = -Real.log (2000000 / 2000533) := by
    rw [show ((2000533 / 2000000) : ℝ) = ((2000000 / 2000533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8814_neg : (53307 / 200000000) ≤ -Real.log (1999467 / 2000000) ∧
    -Real.log (1999467 / 2000000) ≤ (33317 / 125000000) := by
  have h := checkLog_sound (w := (533 / 3999467)) (n := 12)
    (lo := (53307 / 200000000)) (hi := (33317 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999467) = 1/(1999467 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8814 : Bounds (-33317 / 125000000) (-53307 / 200000000) (Real.log (1999467 / 2000000)) := by
  have h := reflection_log_8814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8815_neg : (126281047 / 1000000000) ≤ -Real.log (1000000 / 1134601) ∧
    -Real.log (1000000 / 1134601) ≤ (15785131 / 125000000) := by
  have h := checkLog_sound (w := (134601 / 2134601)) (n := 12)
    (lo := (126281047 / 1000000000)) (hi := (15785131 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1134601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1134601 / 1000000) = 1/(1000000 / 1134601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8815 : Bounds (126281047 / 1000000000) (15785131 / 125000000) (Real.log (1134601 / 1000000)) := by
  have h := reflection_log_8815_neg
  have he : Real.log (1134601 / 1000000) = -Real.log (1000000 / 1134601) := by
    rw [show ((1134601 / 1000000) : ℝ) = ((1000000 / 1134601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8816_neg : (72282303 / 500000000) ≤ -Real.log (865399 / 1000000) ∧
    -Real.log (865399 / 1000000) ≤ (144564607 / 1000000000) := by
  have h := checkLog_sound (w := (134601 / 1865399)) (n := 12)
    (lo := (72282303 / 500000000)) (hi := (144564607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 865399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 865399) = 1/(865399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8816 : Bounds (-144564607 / 1000000000) (-72282303 / 500000000) (Real.log (865399 / 1000000)) := by
  have h := reflection_log_8816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8817_neg : (126742777 / 1000000000) ≤ -Real.log (8000 / 9081) ∧
    -Real.log (8000 / 9081) ≤ (63371389 / 500000000) := by
  have h := checkLog_sound (w := (1081 / 17081)) (n := 12)
    (lo := (126742777 / 1000000000)) (hi := (63371389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9081 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9081 / 8000) = 1/(8000 / 9081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8817 : Bounds (126742777 / 1000000000) (63371389 / 500000000) (Real.log (9081 / 8000)) := by
  have h := reflection_log_8817_neg
  have he : Real.log (9081 / 8000) = -Real.log (8000 / 9081) := by
    rw [show ((9081 / 8000) : ℝ) = ((8000 / 9081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8818_neg : (145170291 / 1000000000) ≤ -Real.log (6919 / 8000) ∧
    -Real.log (6919 / 8000) ≤ (36292573 / 250000000) := by
  have h := checkLog_sound (w := (1081 / 14919)) (n := 12)
    (lo := (145170291 / 1000000000)) (hi := (36292573 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 6919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 6919) = 1/(6919 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8818 : Bounds (-36292573 / 250000000) (-145170291 / 1000000000) (Real.log (6919 / 8000)) := by
  have h := reflection_log_8818_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8819_neg : (9213757 / 500000000) ≤ -Real.log (62831439 / 64000000) ∧
    -Real.log (62831439 / 64000000) ≤ (3685503 / 200000000) := by
  have h := checkLog_sound (w := (1168561 / 126831439)) (n := 12)
    (lo := (9213757 / 500000000)) (hi := (3685503 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64000000 / 62831439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64000000 / 62831439) = 1/(62831439 / 64000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8819 : Bounds (-3685503 / 200000000) (-9213757 / 500000000) (Real.log (62831439 / 64000000)) := by
  have h := reflection_log_8819_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8820_neg : (18283559 / 1000000000) ≤ -Real.log (981882570799 / 1000000000000) ∧
    -Real.log (981882570799 / 1000000000000) ≤ (457089 / 25000000) := by
  have h := checkLog_sound (w := (18117429201 / 1981882570799)) (n := 12)
    (lo := (18283559 / 1000000000)) (hi := (457089 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981882570799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981882570799) = 1/(981882570799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8820 : Bounds (-457089 / 25000000) (-18283559 / 1000000000) (Real.log (981882570799 / 1000000000000)) := by
  have h := reflection_log_8820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8821_neg : (135422827 / 500000000) ≤ -Real.log (500000000000 / 655536347973) ∧
    -Real.log (500000000000 / 655536347973) ≤ (54169131 / 200000000) := by
  have h := checkLog_sound (w := (155536347973 / 1155536347973)) (n := 12)
    (lo := (135422827 / 500000000)) (hi := (54169131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655536347973 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655536347973 / 500000000000) = 1/(500000000000 / 655536347973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8821 : Bounds (135422827 / 500000000) (54169131 / 200000000) (Real.log (655536347973 / 500000000000)) := by
  have h := reflection_log_8821_neg
  have he : Real.log (655536347973 / 500000000000) = -Real.log (500000000000 / 655536347973) := by
    rw [show ((655536347973 / 500000000000) : ℝ) = ((500000000000 / 655536347973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8822_neg : (67978267 / 250000000) ≤ -Real.log (100000000000 / 131247290071) ∧
    -Real.log (100000000000 / 131247290071) ≤ (271913069 / 1000000000) := by
  have h := checkLog_sound (w := (31247290071 / 231247290071)) (n := 12)
    (lo := (67978267 / 250000000)) (hi := (271913069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131247290071 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131247290071 / 100000000000) = 1/(100000000000 / 131247290071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8822 : Bounds (67978267 / 250000000) (271913069 / 1000000000) (Real.log (131247290071 / 100000000000)) := by
  have h := reflection_log_8822_neg
  have he : Real.log (131247290071 / 100000000000) = -Real.log (100000000000 / 131247290071) := by
    rw [show ((131247290071 / 100000000000) : ℝ) = ((100000000000 / 131247290071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8823_neg : (272554287 / 500000000) ≤ -Real.log (500000000000 / 862397820163) ∧
    -Real.log (500000000000 / 862397820163) ≤ (21804343 / 40000000) := by
  have h := checkLog_sound (w := (362397820163 / 1362397820163)) (n := 12)
    (lo := (272554287 / 500000000)) (hi := (21804343 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((862397820163 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(862397820163 / 500000000000) = 1/(500000000000 / 862397820163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8823 : Bounds (272554287 / 500000000) (21804343 / 40000000) (Real.log (862397820163 / 500000000000)) := by
  have h := reflection_log_8823_neg
  have he : Real.log (862397820163 / 500000000000) = -Real.log (500000000000 / 862397820163) := by
    rw [show ((862397820163 / 500000000000) : ℝ) = ((500000000000 / 862397820163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8824_neg : (546184871 / 1000000000) ≤ -Real.log (500000000000 / 863326516701) ∧
    -Real.log (500000000000 / 863326516701) ≤ (68273109 / 125000000) := by
  have h := checkLog_sound (w := (363326516701 / 1363326516701)) (n := 12)
    (lo := (546184871 / 1000000000)) (hi := (68273109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((863326516701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(863326516701 / 500000000000) = 1/(500000000000 / 863326516701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8824 : Bounds (546184871 / 1000000000) (68273109 / 125000000) (Real.log (863326516701 / 500000000000)) := by
  have h := reflection_log_8824_neg
  have he : Real.log (863326516701 / 500000000000) = -Real.log (500000000000 / 863326516701) := by
    rw [show ((863326516701 / 500000000000) : ℝ) = ((500000000000 / 863326516701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8825_neg : (236651901 / 1000000000) ≤ -Real.log (1000 / 1267) ∧
    -Real.log (1000 / 1267) ≤ (118325951 / 500000000) := by
  have h := checkLog_sound (w := (267 / 2267)) (n := 12)
    (lo := (236651901 / 1000000000)) (hi := (118325951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267 / 1000) = 1/(1000 / 1267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8825 : Bounds (236651901 / 1000000000) (118325951 / 500000000) (Real.log (1267 / 1000)) := by
  have h := reflection_log_8825_neg
  have he : Real.log (1267 / 1000) = -Real.log (1000 / 1267) := by
    rw [show ((1267 / 1000) : ℝ) = ((1000 / 1267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8826_neg : (310609577 / 1000000000) ≤ -Real.log (733 / 1000) ∧
    -Real.log (733 / 1000) ≤ (155304789 / 500000000) := by
  have h := checkLog_sound (w := (267 / 1733)) (n := 12)
    (lo := (310609577 / 1000000000)) (hi := (155304789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 733) = 1/(733 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8826 : Bounds (-155304789 / 500000000) (-310609577 / 1000000000) (Real.log (733 / 1000)) := by
  have h := reflection_log_8826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8827_neg : (66741 / 250000000) ≤ -Real.log (1000000 / 1000267) ∧
    -Real.log (1000000 / 1000267) ≤ (53393 / 200000000) := by
  have h := checkLog_sound (w := (267 / 2000267)) (n := 12)
    (lo := (66741 / 250000000)) (hi := (53393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000267 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000267 / 1000000) = 1/(1000000 / 1000267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8827 : Bounds (66741 / 250000000) (53393 / 200000000) (Real.log (1000267 / 1000000)) := by
  have h := reflection_log_8827_neg
  have he : Real.log (1000267 / 1000000) = -Real.log (1000000 / 1000267) := by
    rw [show ((1000267 / 1000000) : ℝ) = ((1000000 / 1000267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8828_neg : (53407 / 200000000) ≤ -Real.log (999733 / 1000000) ∧
    -Real.log (999733 / 1000000) ≤ (66759 / 250000000) := by
  have h := checkLog_sound (w := (267 / 1999733)) (n := 12)
    (lo := (53407 / 200000000)) (hi := (66759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999733) = 1/(999733 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8828 : Bounds (-66759 / 250000000) (-53407 / 200000000) (Real.log (999733 / 1000000)) := by
  have h := reflection_log_8828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8829_neg : (3953443 / 31250000) ≤ -Real.log (1000000 / 1134861) ∧
    -Real.log (1000000 / 1134861) ≤ (126510177 / 1000000000) := by
  have h := checkLog_sound (w := (134861 / 2134861)) (n := 12)
    (lo := (3953443 / 31250000)) (hi := (126510177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1134861 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1134861 / 1000000) = 1/(1000000 / 1134861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8829 : Bounds (3953443 / 31250000) (126510177 / 1000000000) (Real.log (1134861 / 1000000)) := by
  have h := reflection_log_8829_neg
  have he : Real.log (1134861 / 1000000) = -Real.log (1000000 / 1134861) := by
    rw [show ((1134861 / 1000000) : ℝ) = ((1000000 / 1134861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8830_neg : (144865091 / 1000000000) ≤ -Real.log (865139 / 1000000) ∧
    -Real.log (865139 / 1000000) ≤ (36216273 / 250000000) := by
  have h := checkLog_sound (w := (134861 / 1865139)) (n := 12)
    (lo := (144865091 / 1000000000)) (hi := (36216273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 865139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 865139) = 1/(865139 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8830 : Bounds (-36216273 / 250000000) (-144865091 / 1000000000) (Real.log (865139 / 1000000)) := by
  have h := reflection_log_8830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8831_neg : (634859 / 5000000) ≤ -Real.log (200000 / 227077) ∧
    -Real.log (200000 / 227077) ≤ (126971801 / 1000000000) := by
  have h := checkLog_sound (w := (27077 / 427077)) (n := 12)
    (lo := (634859 / 5000000)) (hi := (126971801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227077 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(227077 / 200000) = 1/(200000 / 227077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8831 : Bounds (634859 / 5000000) (126971801 / 1000000000) (Real.log (227077 / 200000)) := by
  have h := reflection_log_8831_neg
  have he : Real.log (227077 / 200000) = -Real.log (200000 / 227077) := by
    rw [show ((227077 / 200000) : ℝ) = ((200000 / 227077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
