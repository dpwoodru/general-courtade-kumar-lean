import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9472_neg : (145021 / 500000000) ≤ -Real.log (99971 / 100000) ∧
    -Real.log (99971 / 100000) ≤ (290043 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 199971)) (n := 12)
    (lo := (145021 / 500000000)) (hi := (290043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99971) = 1/(99971 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9472 : Bounds (-290043 / 1000000000) (-145021 / 500000000) (Real.log (99971 / 100000)) := by
  have h := reflection_log_9472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9473_neg : (137019053 / 1000000000) ≤ -Real.log (20000 / 22937) ∧
    -Real.log (20000 / 22937) ≤ (68509527 / 500000000) := by
  have h := checkLog_sound (w := (2937 / 42937)) (n := 12)
    (lo := (137019053 / 1000000000)) (hi := (68509527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22937 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22937 / 20000) = 1/(20000 / 22937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9473 : Bounds (137019053 / 1000000000) (68509527 / 500000000) (Real.log (22937 / 20000)) := by
  have h := reflection_log_9473_neg
  have he : Real.log (22937 / 20000) = -Real.log (20000 / 22937) := by
    rw [show ((22937 / 20000) : ℝ) = ((20000 / 22937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9474_neg : (158819897 / 1000000000) ≤ -Real.log (17063 / 20000) ∧
    -Real.log (17063 / 20000) ≤ (79409949 / 500000000) := by
  have h := checkLog_sound (w := (2937 / 37063)) (n := 12)
    (lo := (158819897 / 1000000000)) (hi := (79409949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 17063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 17063) = 1/(17063 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9474 : Bounds (-79409949 / 500000000) (-158819897 / 1000000000) (Real.log (17063 / 20000)) := by
  have h := reflection_log_9474_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9475_neg : (13749677 / 100000000) ≤ -Real.log (500000 / 573699) ∧
    -Real.log (500000 / 573699) ≤ (137496771 / 1000000000) := by
  have h := checkLog_sound (w := (73699 / 1073699)) (n := 12)
    (lo := (13749677 / 100000000)) (hi := (137496771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((573699 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(573699 / 500000) = 1/(500000 / 573699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9475 : Bounds (13749677 / 100000000) (137496771 / 1000000000) (Real.log (573699 / 500000)) := by
  have h := reflection_log_9475_neg
  have he : Real.log (573699 / 500000) = -Real.log (500000 / 573699) := by
    rw [show ((573699 / 500000) : ℝ) = ((500000 / 573699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9476_neg : (39865607 / 250000000) ≤ -Real.log (426301 / 500000) ∧
    -Real.log (426301 / 500000) ≤ (159462429 / 1000000000) := by
  have h := checkLog_sound (w := (73699 / 926301)) (n := 12)
    (lo := (39865607 / 250000000)) (hi := (159462429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 426301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 426301) = 1/(426301 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9476 : Bounds (-159462429 / 1000000000) (-39865607 / 250000000) (Real.log (426301 / 500000)) := by
  have h := reflection_log_9476_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9477_neg : (10982829 / 500000000) ≤ -Real.log (244568457399 / 250000000000) ∧
    -Real.log (244568457399 / 250000000000) ≤ (21965659 / 1000000000) := by
  have h := checkLog_sound (w := (5431542601 / 494568457399)) (n := 12)
    (lo := (10982829 / 500000000)) (hi := (21965659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244568457399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244568457399) = 1/(244568457399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9477 : Bounds (-21965659 / 1000000000) (-10982829 / 500000000) (Real.log (244568457399 / 250000000000)) := by
  have h := reflection_log_9477_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9478_neg : (21800843 / 1000000000) ≤ -Real.log (391374031 / 400000000) ∧
    -Real.log (391374031 / 400000000) ≤ (5450211 / 250000000) := by
  have h := checkLog_sound (w := (8625969 / 791374031)) (n := 12)
    (lo := (21800843 / 1000000000)) (hi := (5450211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 391374031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 391374031) = 1/(391374031 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9478 : Bounds (-5450211 / 250000000) (-21800843 / 1000000000) (Real.log (391374031 / 400000000)) := by
  have h := reflection_log_9478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9479_neg : (5916779 / 20000000) ≤ -Real.log (250000000000 / 336063412061) ∧
    -Real.log (250000000000 / 336063412061) ≤ (295838951 / 1000000000) := by
  have h := checkLog_sound (w := (86063412061 / 586063412061)) (n := 12)
    (lo := (5916779 / 20000000)) (hi := (295838951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336063412061 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336063412061 / 250000000000) = 1/(250000000000 / 336063412061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9479 : Bounds (5916779 / 20000000) (295838951 / 1000000000) (Real.log (336063412061 / 250000000000)) := by
  have h := reflection_log_9479_neg
  have he : Real.log (336063412061 / 250000000000) = -Real.log (250000000000 / 336063412061) := by
    rw [show ((336063412061 / 250000000000) : ℝ) = ((250000000000 / 336063412061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9480_neg : (296959199 / 1000000000) ≤ -Real.log (25000000000 / 33644009749) ∧
    -Real.log (25000000000 / 33644009749) ≤ (371199 / 1250000) := by
  have h := checkLog_sound (w := (8644009749 / 58644009749)) (n := 12)
    (lo := (296959199 / 1000000000)) (hi := (371199 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33644009749 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33644009749 / 25000000000) = 1/(25000000000 / 33644009749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9480 : Bounds (296959199 / 1000000000) (371199 / 1250000) (Real.log (33644009749 / 25000000000)) := by
  have h := reflection_log_9480_neg
  have he : Real.log (33644009749 / 25000000000) = -Real.log (25000000000 / 33644009749) := by
    rw [show ((33644009749 / 25000000000) : ℝ) = ((25000000000 / 33644009749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9481_neg : (596040877 / 1000000000) ≤ -Real.log (250000000000 / 453729767769) ∧
    -Real.log (250000000000 / 453729767769) ≤ (298020439 / 500000000) := by
  have h := checkLog_sound (w := (203729767769 / 703729767769)) (n := 12)
    (lo := (596040877 / 1000000000)) (hi := (298020439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((453729767769 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(453729767769 / 250000000000) = 1/(250000000000 / 453729767769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9481 : Bounds (596040877 / 1000000000) (298020439 / 500000000) (Real.log (453729767769 / 250000000000)) := by
  have h := reflection_log_9481_neg
  have he : Real.log (453729767769 / 250000000000) = -Real.log (250000000000 / 453729767769) := by
    rw [show ((453729767769 / 250000000000) : ℝ) = ((250000000000 / 453729767769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9482_neg : (597132527 / 1000000000) ≤ -Real.log (250000000000 / 454225352113) ∧
    -Real.log (250000000000 / 454225352113) ≤ (37320783 / 62500000) := by
  have h := checkLog_sound (w := (204225352113 / 704225352113)) (n := 12)
    (lo := (597132527 / 1000000000)) (hi := (37320783 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((454225352113 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(454225352113 / 250000000000) = 1/(250000000000 / 454225352113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9482 : Bounds (597132527 / 1000000000) (37320783 / 62500000) (Real.log (454225352113 / 250000000000)) := by
  have h := reflection_log_9482_neg
  have he : Real.log (454225352113 / 250000000000) = -Real.log (250000000000 / 454225352113) := by
    rw [show ((454225352113 / 250000000000) : ℝ) = ((250000000000 / 454225352113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9483_neg : (12751487 / 50000000) ≤ -Real.log (2000 / 2581) ∧
    -Real.log (2000 / 2581) ≤ (255029741 / 1000000000) := by
  have h := checkLog_sound (w := (581 / 4581)) (n := 12)
    (lo := (12751487 / 50000000)) (hi := (255029741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2581 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2581 / 2000) = 1/(2000 / 2581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9483 : Bounds (12751487 / 50000000) (255029741 / 1000000000) (Real.log (2581 / 2000)) := by
  have h := reflection_log_9483_neg
  have he : Real.log (2581 / 2000) = -Real.log (2000 / 2581) := by
    rw [show ((2581 / 2000) : ℝ) = ((2000 / 2581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9484_neg : (171597391 / 500000000) ≤ -Real.log (1419 / 2000) ∧
    -Real.log (1419 / 2000) ≤ (343194783 / 1000000000) := by
  have h := checkLog_sound (w := (581 / 3419)) (n := 12)
    (lo := (171597391 / 500000000)) (hi := (343194783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1419) = 1/(1419 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9484 : Bounds (-343194783 / 1000000000) (-171597391 / 500000000) (Real.log (1419 / 2000)) := by
  have h := reflection_log_9484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9485_neg : (290457 / 1000000000) ≤ -Real.log (2000000 / 2000581) ∧
    -Real.log (2000000 / 2000581) ≤ (145229 / 500000000) := by
  have h := checkLog_sound (w := (581 / 4000581)) (n := 12)
    (lo := (290457 / 1000000000)) (hi := (145229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000581 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000581 / 2000000) = 1/(2000000 / 2000581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9485 : Bounds (290457 / 1000000000) (145229 / 500000000) (Real.log (2000581 / 2000000)) := by
  have h := reflection_log_9485_neg
  have he : Real.log (2000581 / 2000000) = -Real.log (2000000 / 2000581) := by
    rw [show ((2000581 / 2000000) : ℝ) = ((2000000 / 2000581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9486_neg : (145271 / 500000000) ≤ -Real.log (1999419 / 2000000) ∧
    -Real.log (1999419 / 2000000) ≤ (290543 / 1000000000) := by
  have h := checkLog_sound (w := (581 / 3999419)) (n := 12)
    (lo := (145271 / 500000000)) (hi := (290543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999419) = 1/(1999419 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9486 : Bounds (-290543 / 1000000000) (-145271 / 500000000) (Real.log (1999419 / 2000000)) := by
  have h := reflection_log_9486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9487_neg : (137247479 / 1000000000) ≤ -Real.log (125000 / 143389) ∧
    -Real.log (125000 / 143389) ≤ (3431187 / 25000000) := by
  have h := checkLog_sound (w := (18389 / 268389)) (n := 12)
    (lo := (137247479 / 1000000000)) (hi := (3431187 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143389 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143389 / 125000) = 1/(125000 / 143389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9487 : Bounds (137247479 / 1000000000) (3431187 / 25000000) (Real.log (143389 / 125000)) := by
  have h := reflection_log_9487_neg
  have he : Real.log (143389 / 125000) = -Real.log (125000 / 143389) := by
    rw [show ((143389 / 125000) : ℝ) = ((125000 / 143389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9488_neg : (159127041 / 1000000000) ≤ -Real.log (106611 / 125000) ∧
    -Real.log (106611 / 125000) ≤ (79563521 / 500000000) := by
  have h := checkLog_sound (w := (18389 / 231611)) (n := 12)
    (lo := (159127041 / 1000000000)) (hi := (79563521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 106611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 106611) = 1/(106611 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9488 : Bounds (-79563521 / 500000000) (-159127041 / 1000000000) (Real.log (106611 / 125000)) := by
  have h := reflection_log_9488_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9489_neg : (68862543 / 500000000) ≤ -Real.log (50000 / 57383) ∧
    -Real.log (50000 / 57383) ≤ (137725087 / 1000000000) := by
  have h := checkLog_sound (w := (7383 / 107383)) (n := 12)
    (lo := (68862543 / 500000000)) (hi := (137725087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57383 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57383 / 50000) = 1/(50000 / 57383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9489 : Bounds (68862543 / 500000000) (137725087 / 1000000000) (Real.log (57383 / 50000)) := by
  have h := reflection_log_9489_neg
  have he : Real.log (57383 / 50000) = -Real.log (50000 / 57383) := by
    rw [show ((57383 / 50000) : ℝ) = ((50000 / 57383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9490_neg : (15976977 / 100000000) ≤ -Real.log (42617 / 50000) ∧
    -Real.log (42617 / 50000) ≤ (159769771 / 1000000000) := by
  have h := checkLog_sound (w := (7383 / 92617)) (n := 12)
    (lo := (15976977 / 100000000)) (hi := (159769771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 42617) = 1/(42617 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9490 : Bounds (-159769771 / 1000000000) (-15976977 / 100000000) (Real.log (42617 / 50000)) := by
  have h := reflection_log_9490_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9491_neg : (22044683 / 1000000000) ≤ -Real.log (2445491311 / 2500000000) ∧
    -Real.log (2445491311 / 2500000000) ≤ (5511171 / 250000000) := by
  have h := checkLog_sound (w := (54508689 / 4945491311)) (n := 12)
    (lo := (22044683 / 1000000000)) (hi := (5511171 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2445491311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2445491311) = 1/(2445491311 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9491 : Bounds (-5511171 / 250000000) (-22044683 / 1000000000) (Real.log (2445491311 / 2500000000)) := by
  have h := reflection_log_9491_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9492_neg : (21879561 / 1000000000) ≤ -Real.log (15286844679 / 15625000000) ∧
    -Real.log (15286844679 / 15625000000) ≤ (10939781 / 500000000) := by
  have h := checkLog_sound (w := (338155321 / 30911844679)) (n := 12)
    (lo := (21879561 / 1000000000)) (hi := (10939781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15286844679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15286844679) = 1/(15286844679 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9492 : Bounds (-10939781 / 500000000) (-21879561 / 1000000000) (Real.log (15286844679 / 15625000000)) := by
  have h := reflection_log_9492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9493_neg : (7409363 / 25000000) ≤ -Real.log (125000000000 / 168121722899) ∧
    -Real.log (125000000000 / 168121722899) ≤ (296374521 / 1000000000) := by
  have h := checkLog_sound (w := (43121722899 / 293121722899)) (n := 12)
    (lo := (7409363 / 25000000)) (hi := (296374521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168121722899 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168121722899 / 125000000000) = 1/(125000000000 / 168121722899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9493 : Bounds (7409363 / 25000000) (296374521 / 1000000000) (Real.log (168121722899 / 125000000000)) := by
  have h := reflection_log_9493_neg
  have he : Real.log (168121722899 / 125000000000) = -Real.log (125000000000 / 168121722899) := by
    rw [show ((168121722899 / 125000000000) : ℝ) = ((125000000000 / 168121722899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9494_neg : (297494857 / 1000000000) ≤ -Real.log (500000000000 / 673240725533) ∧
    -Real.log (500000000000 / 673240725533) ≤ (148747429 / 500000000) := by
  have h := checkLog_sound (w := (173240725533 / 1173240725533)) (n := 12)
    (lo := (297494857 / 1000000000)) (hi := (148747429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673240725533 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673240725533 / 500000000000) = 1/(500000000000 / 673240725533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9494 : Bounds (297494857 / 1000000000) (148747429 / 500000000) (Real.log (673240725533 / 500000000000)) := by
  have h := reflection_log_9494_neg
  have he : Real.log (673240725533 / 500000000000) = -Real.log (500000000000 / 673240725533) := by
    rw [show ((673240725533 / 500000000000) : ℝ) = ((500000000000 / 673240725533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9495_neg : (597132527 / 1000000000) ≤ -Real.log (20000000000 / 36338028169) ∧
    -Real.log (20000000000 / 36338028169) ≤ (37320783 / 62500000) := by
  have h := checkLog_sound (w := (16338028169 / 56338028169)) (n := 12)
    (lo := (597132527 / 1000000000)) (hi := (37320783 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36338028169 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36338028169 / 20000000000) = 1/(20000000000 / 36338028169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9495 : Bounds (597132527 / 1000000000) (37320783 / 62500000) (Real.log (36338028169 / 20000000000)) := by
  have h := reflection_log_9495_neg
  have he : Real.log (36338028169 / 20000000000) = -Real.log (20000000000 / 36338028169) := by
    rw [show ((36338028169 / 20000000000) : ℝ) = ((20000000000 / 36338028169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9496_neg : (299112261 / 500000000) ≤ -Real.log (500000000000 / 909443269909) ∧
    -Real.log (500000000000 / 909443269909) ≤ (598224523 / 1000000000) := by
  have h := checkLog_sound (w := (409443269909 / 1409443269909)) (n := 12)
    (lo := (299112261 / 500000000)) (hi := (598224523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((909443269909 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(909443269909 / 500000000000) = 1/(500000000000 / 909443269909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9496 : Bounds (299112261 / 500000000) (598224523 / 1000000000) (Real.log (909443269909 / 500000000000)) := by
  have h := reflection_log_9496_neg
  have he : Real.log (909443269909 / 500000000000) = -Real.log (500000000000 / 909443269909) := by
    rw [show ((909443269909 / 500000000000) : ℝ) = ((500000000000 / 909443269909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9497_neg : (255417111 / 1000000000) ≤ -Real.log (1000 / 1291) ∧
    -Real.log (1000 / 1291) ≤ (31927139 / 125000000) := by
  have h := checkLog_sound (w := (291 / 2291)) (n := 12)
    (lo := (255417111 / 1000000000)) (hi := (31927139 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1291 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1291 / 1000) = 1/(1000 / 1291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9497 : Bounds (255417111 / 1000000000) (31927139 / 125000000) (Real.log (1291 / 1000)) := by
  have h := reflection_log_9497_neg
  have he : Real.log (1291 / 1000) = -Real.log (1000 / 1291) := by
    rw [show ((1291 / 1000) : ℝ) = ((1000 / 1291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9498_neg : (42987469 / 125000000) ≤ -Real.log (709 / 1000) ∧
    -Real.log (709 / 1000) ≤ (343899753 / 1000000000) := by
  have h := checkLog_sound (w := (291 / 1709)) (n := 12)
    (lo := (42987469 / 125000000)) (hi := (343899753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 709) = 1/(709 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9498 : Bounds (-343899753 / 1000000000) (-42987469 / 125000000) (Real.log (709 / 1000)) := by
  have h := reflection_log_9498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9499_neg : (290957 / 1000000000) ≤ -Real.log (1000000 / 1000291) ∧
    -Real.log (1000000 / 1000291) ≤ (145479 / 500000000) := by
  have h := checkLog_sound (w := (291 / 2000291)) (n := 12)
    (lo := (290957 / 1000000000)) (hi := (145479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000291 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000291 / 1000000) = 1/(1000000 / 1000291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9499 : Bounds (290957 / 1000000000) (145479 / 500000000) (Real.log (1000291 / 1000000)) := by
  have h := reflection_log_9499_neg
  have he : Real.log (1000291 / 1000000) = -Real.log (1000000 / 1000291) := by
    rw [show ((1000291 / 1000000) : ℝ) = ((1000000 / 1000291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9500_neg : (145521 / 500000000) ≤ -Real.log (999709 / 1000000) ∧
    -Real.log (999709 / 1000000) ≤ (291043 / 1000000000) := by
  have h := checkLog_sound (w := (291 / 1999709)) (n := 12)
    (lo := (145521 / 500000000)) (hi := (291043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999709) = 1/(999709 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9500 : Bounds (-291043 / 1000000000) (-145521 / 500000000) (Real.log (999709 / 1000000)) := by
  have h := reflection_log_9500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9501_neg : (137475853 / 1000000000) ≤ -Real.log (500000 / 573687) ∧
    -Real.log (500000 / 573687) ≤ (68737927 / 500000000) := by
  have h := checkLog_sound (w := (73687 / 1073687)) (n := 12)
    (lo := (137475853 / 1000000000)) (hi := (68737927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((573687 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(573687 / 500000) = 1/(500000 / 573687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9501 : Bounds (137475853 / 1000000000) (68737927 / 500000000) (Real.log (573687 / 500000)) := by
  have h := reflection_log_9501_neg
  have he : Real.log (573687 / 500000) = -Real.log (500000 / 573687) := by
    rw [show ((573687 / 500000) : ℝ) = ((500000 / 573687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9502_neg : (3985857 / 25000000) ≤ -Real.log (426313 / 500000) ∧
    -Real.log (426313 / 500000) ≤ (159434281 / 1000000000) := by
  have h := checkLog_sound (w := (73687 / 926313)) (n := 12)
    (lo := (3985857 / 25000000)) (hi := (159434281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 426313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 426313) = 1/(426313 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9502 : Bounds (-159434281 / 1000000000) (-3985857 / 25000000) (Real.log (426313 / 500000)) := by
  have h := reflection_log_9502_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9503_neg : (68977111 / 500000000) ≤ -Real.log (1000000 / 1147923) ∧
    -Real.log (1000000 / 1147923) ≤ (137954223 / 1000000000) := by
  have h := checkLog_sound (w := (147923 / 2147923)) (n := 12)
    (lo := (68977111 / 500000000)) (hi := (137954223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1147923 / 1000000) = 1/(1000000 / 1147923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9503 : Bounds (68977111 / 500000000) (137954223 / 1000000000) (Real.log (1147923 / 1000000)) := by
  have h := reflection_log_9503_neg
  have he : Real.log (1147923 / 1000000) = -Real.log (1000000 / 1147923) := by
    rw [show ((1147923 / 1000000) : ℝ) = ((1000000 / 1147923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9504_neg : (8003919 / 50000000) ≤ -Real.log (852077 / 1000000) ∧
    -Real.log (852077 / 1000000) ≤ (160078381 / 1000000000) := by
  have h := checkLog_sound (w := (147923 / 1852077)) (n := 12)
    (lo := (8003919 / 50000000)) (hi := (160078381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 852077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 852077) = 1/(852077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9504 : Bounds (-160078381 / 1000000000) (-8003919 / 50000000) (Real.log (852077 / 1000000)) := by
  have h := reflection_log_9504_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9505_neg : (11062079 / 500000000) ≤ -Real.log (978118786071 / 1000000000000) ∧
    -Real.log (978118786071 / 1000000000000) ≤ (22124159 / 1000000000) := by
  have h := checkLog_sound (w := (21881213929 / 1978118786071)) (n := 12)
    (lo := (11062079 / 500000000)) (hi := (22124159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978118786071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978118786071) = 1/(978118786071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9505 : Bounds (-22124159 / 1000000000) (-11062079 / 500000000) (Real.log (978118786071 / 1000000000000)) := by
  have h := reflection_log_9505_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9506_neg : (21958427 / 1000000000) ≤ -Real.log (244570226031 / 250000000000) ∧
    -Real.log (244570226031 / 250000000000) ≤ (5489607 / 250000000) := by
  have h := checkLog_sound (w := (5429773969 / 494570226031)) (n := 12)
    (lo := (21958427 / 1000000000)) (hi := (5489607 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244570226031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244570226031) = 1/(244570226031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9506 : Bounds (-5489607 / 250000000) (-21958427 / 1000000000) (Real.log (244570226031 / 250000000000)) := by
  have h := reflection_log_9506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9507_neg : (296910133 / 1000000000) ≤ -Real.log (250000000000 / 336423590179) ∧
    -Real.log (250000000000 / 336423590179) ≤ (148455067 / 500000000) := by
  have h := checkLog_sound (w := (86423590179 / 586423590179)) (n := 12)
    (lo := (296910133 / 1000000000)) (hi := (148455067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336423590179 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336423590179 / 250000000000) = 1/(250000000000 / 336423590179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9507 : Bounds (296910133 / 1000000000) (148455067 / 500000000) (Real.log (336423590179 / 250000000000)) := by
  have h := reflection_log_9507_neg
  have he : Real.log (336423590179 / 250000000000) = -Real.log (250000000000 / 336423590179) := by
    rw [show ((336423590179 / 250000000000) : ℝ) = ((250000000000 / 336423590179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9508_neg : (298032603 / 1000000000) ≤ -Real.log (250000000000 / 336801427571) ∧
    -Real.log (250000000000 / 336801427571) ≤ (74508151 / 250000000) := by
  have h := checkLog_sound (w := (86801427571 / 586801427571)) (n := 12)
    (lo := (298032603 / 1000000000)) (hi := (74508151 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336801427571 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336801427571 / 250000000000) = 1/(250000000000 / 336801427571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9508 : Bounds (298032603 / 1000000000) (74508151 / 250000000) (Real.log (336801427571 / 250000000000)) := by
  have h := reflection_log_9508_neg
  have he : Real.log (336801427571 / 250000000000) = -Real.log (250000000000 / 336801427571) := by
    rw [show ((336801427571 / 250000000000) : ℝ) = ((250000000000 / 336801427571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9509_neg : (299112261 / 500000000) ≤ -Real.log (125000000000 / 227360817477) ∧
    -Real.log (125000000000 / 227360817477) ≤ (598224523 / 1000000000) := by
  have h := checkLog_sound (w := (102360817477 / 352360817477)) (n := 12)
    (lo := (299112261 / 500000000)) (hi := (598224523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227360817477 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(227360817477 / 125000000000) = 1/(125000000000 / 227360817477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9509 : Bounds (299112261 / 500000000) (598224523 / 1000000000) (Real.log (227360817477 / 125000000000)) := by
  have h := reflection_log_9509_neg
  have he : Real.log (227360817477 / 125000000000) = -Real.log (125000000000 / 227360817477) := by
    rw [show ((227360817477 / 125000000000) : ℝ) = ((125000000000 / 227360817477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9510_neg : (4682163 / 7812500) ≤ -Real.log (62500000000 / 113804654443) ∧
    -Real.log (62500000000 / 113804654443) ≤ (119863373 / 200000000) := by
  have h := checkLog_sound (w := (51304654443 / 176304654443)) (n := 12)
    (lo := (4682163 / 7812500)) (hi := (119863373 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113804654443 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113804654443 / 62500000000) = 1/(62500000000 / 113804654443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9510 : Bounds (4682163 / 7812500) (119863373 / 200000000) (Real.log (113804654443 / 62500000000)) := by
  have h := reflection_log_9510_neg
  have he : Real.log (113804654443 / 62500000000) = -Real.log (62500000000 / 113804654443) := by
    rw [show ((113804654443 / 62500000000) : ℝ) = ((62500000000 / 113804654443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9511_neg : (255804333 / 1000000000) ≤ -Real.log (2000 / 2583) ∧
    -Real.log (2000 / 2583) ≤ (127902167 / 500000000) := by
  have h := checkLog_sound (w := (583 / 4583)) (n := 12)
    (lo := (255804333 / 1000000000)) (hi := (127902167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2583 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2583 / 2000) = 1/(2000 / 2583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9511 : Bounds (255804333 / 1000000000) (127902167 / 500000000) (Real.log (2583 / 2000)) := by
  have h := reflection_log_9511_neg
  have he : Real.log (2583 / 2000) = -Real.log (2000 / 2583) := by
    rw [show ((2583 / 2000) : ℝ) = ((2000 / 2583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9512_neg : (344605219 / 1000000000) ≤ -Real.log (1417 / 2000) ∧
    -Real.log (1417 / 2000) ≤ (17230261 / 50000000) := by
  have h := checkLog_sound (w := (583 / 3417)) (n := 12)
    (lo := (344605219 / 1000000000)) (hi := (17230261 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1417) = 1/(1417 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9512 : Bounds (-17230261 / 50000000) (-344605219 / 1000000000) (Real.log (1417 / 2000)) := by
  have h := reflection_log_9512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9513_neg : (291457 / 1000000000) ≤ -Real.log (2000000 / 2000583) ∧
    -Real.log (2000000 / 2000583) ≤ (145729 / 500000000) := by
  have h := checkLog_sound (w := (583 / 4000583)) (n := 12)
    (lo := (291457 / 1000000000)) (hi := (145729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000583 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000583 / 2000000) = 1/(2000000 / 2000583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9513 : Bounds (291457 / 1000000000) (145729 / 500000000) (Real.log (2000583 / 2000000)) := by
  have h := reflection_log_9513_neg
  have he : Real.log (2000583 / 2000000) = -Real.log (2000000 / 2000583) := by
    rw [show ((2000583 / 2000000) : ℝ) = ((2000000 / 2000583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9514_neg : (145771 / 500000000) ≤ -Real.log (1999417 / 2000000) ∧
    -Real.log (1999417 / 2000000) ≤ (291543 / 1000000000) := by
  have h := checkLog_sound (w := (583 / 3999417)) (n := 12)
    (lo := (145771 / 500000000)) (hi := (291543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999417) = 1/(1999417 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9514 : Bounds (-291543 / 1000000000) (-145771 / 500000000) (Real.log (1999417 / 2000000)) := by
  have h := reflection_log_9514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9515_neg : (137703303 / 1000000000) ≤ -Real.log (200000 / 229527) ∧
    -Real.log (200000 / 229527) ≤ (17212913 / 125000000) := by
  have h := checkLog_sound (w := (29527 / 429527)) (n := 12)
    (lo := (137703303 / 1000000000)) (hi := (17212913 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229527 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229527 / 200000) = 1/(200000 / 229527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9515 : Bounds (137703303 / 1000000000) (17212913 / 125000000) (Real.log (229527 / 200000)) := by
  have h := reflection_log_9515_neg
  have he : Real.log (229527 / 200000) = -Real.log (200000 / 229527) := by
    rw [show ((229527 / 200000) : ℝ) = ((200000 / 229527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9516_neg : (3993511 / 25000000) ≤ -Real.log (170473 / 200000) ∧
    -Real.log (170473 / 200000) ≤ (159740441 / 1000000000) := by
  have h := checkLog_sound (w := (29527 / 370473)) (n := 12)
    (lo := (3993511 / 25000000)) (hi := (159740441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 170473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 170473) = 1/(170473 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9516 : Bounds (-159740441 / 1000000000) (-3993511 / 25000000) (Real.log (170473 / 200000)) := by
  have h := reflection_log_9516_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9517_neg : (69091217 / 500000000) ≤ -Real.log (200000 / 229637) ∧
    -Real.log (200000 / 229637) ≤ (27636487 / 200000000) := by
  have h := checkLog_sound (w := (29637 / 429637)) (n := 12)
    (lo := (69091217 / 500000000)) (hi := (27636487 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229637 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229637 / 200000) = 1/(200000 / 229637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9517 : Bounds (69091217 / 500000000) (27636487 / 200000000) (Real.log (229637 / 200000)) := by
  have h := reflection_log_9517_neg
  have he : Real.log (229637 / 200000) = -Real.log (200000 / 229637) := by
    rw [show ((229637 / 200000) : ℝ) = ((200000 / 229637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9518_neg : (160385911 / 1000000000) ≤ -Real.log (170363 / 200000) ∧
    -Real.log (170363 / 200000) ≤ (20048239 / 125000000) := by
  have h := checkLog_sound (w := (29637 / 370363)) (n := 12)
    (lo := (160385911 / 1000000000)) (hi := (20048239 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 170363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 170363) = 1/(170363 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9518 : Bounds (-20048239 / 125000000) (-160385911 / 1000000000) (Real.log (170363 / 200000)) := by
  have h := reflection_log_9518_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9519_neg : (22203477 / 1000000000) ≤ -Real.log (39121648231 / 40000000000) ∧
    -Real.log (39121648231 / 40000000000) ≤ (11101739 / 500000000) := by
  have h := checkLog_sound (w := (878351769 / 79121648231)) (n := 12)
    (lo := (22203477 / 1000000000)) (hi := (11101739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39121648231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39121648231) = 1/(39121648231 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9519 : Bounds (-11101739 / 500000000) (-22203477 / 1000000000) (Real.log (39121648231 / 40000000000)) := by
  have h := reflection_log_9519_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9520_neg : (22037137 / 1000000000) ≤ -Real.log (39128156271 / 40000000000) ∧
    -Real.log (39128156271 / 40000000000) ≤ (11018569 / 500000000) := by
  have h := checkLog_sound (w := (871843729 / 79128156271)) (n := 12)
    (lo := (22037137 / 1000000000)) (hi := (11018569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39128156271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39128156271) = 1/(39128156271 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9520 : Bounds (-11018569 / 500000000) (-22037137 / 1000000000) (Real.log (39128156271 / 40000000000)) := by
  have h := reflection_log_9520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9521_neg : (297443743 / 1000000000) ≤ -Real.log (125000000000 / 168301578549) ∧
    -Real.log (125000000000 / 168301578549) ≤ (9295117 / 31250000) := by
  have h := checkLog_sound (w := (43301578549 / 293301578549)) (n := 12)
    (lo := (297443743 / 1000000000)) (hi := (9295117 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168301578549 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168301578549 / 125000000000) = 1/(125000000000 / 168301578549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9521 : Bounds (297443743 / 1000000000) (9295117 / 31250000) (Real.log (168301578549 / 125000000000)) := by
  have h := reflection_log_9521_neg
  have he : Real.log (168301578549 / 125000000000) = -Real.log (125000000000 / 168301578549) := by
    rw [show ((168301578549 / 125000000000) : ℝ) = ((125000000000 / 168301578549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9522_neg : (149284173 / 500000000) ≤ -Real.log (20000000000 / 26958553207) ∧
    -Real.log (20000000000 / 26958553207) ≤ (298568347 / 1000000000) := by
  have h := checkLog_sound (w := (6958553207 / 46958553207)) (n := 12)
    (lo := (149284173 / 500000000)) (hi := (298568347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26958553207 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26958553207 / 20000000000) = 1/(20000000000 / 26958553207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9522 : Bounds (149284173 / 500000000) (298568347 / 1000000000) (Real.log (26958553207 / 20000000000)) := by
  have h := reflection_log_9522_neg
  have he : Real.log (26958553207 / 20000000000) = -Real.log (20000000000 / 26958553207) := by
    rw [show ((26958553207 / 20000000000) : ℝ) = ((20000000000 / 26958553207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9523_neg : (4682163 / 7812500) ≤ -Real.log (500000000000 / 910437235543) ∧
    -Real.log (500000000000 / 910437235543) ≤ (119863373 / 200000000) := by
  have h := checkLog_sound (w := (410437235543 / 1410437235543)) (n := 12)
    (lo := (4682163 / 7812500)) (hi := (119863373 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((910437235543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(910437235543 / 500000000000) = 1/(500000000000 / 910437235543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9523 : Bounds (4682163 / 7812500) (119863373 / 200000000) (Real.log (910437235543 / 500000000000)) := by
  have h := reflection_log_9523_neg
  have he : Real.log (910437235543 / 500000000000) = -Real.log (500000000000 / 910437235543) := by
    rw [show ((910437235543 / 500000000000) : ℝ) = ((500000000000 / 910437235543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9524_neg : (600409553 / 1000000000) ≤ -Real.log (250000000000 / 455716302047) ∧
    -Real.log (250000000000 / 455716302047) ≤ (300204777 / 500000000) := by
  have h := checkLog_sound (w := (205716302047 / 705716302047)) (n := 12)
    (lo := (600409553 / 1000000000)) (hi := (300204777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((455716302047 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(455716302047 / 250000000000) = 1/(250000000000 / 455716302047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9524 : Bounds (600409553 / 1000000000) (300204777 / 500000000) (Real.log (455716302047 / 250000000000)) := by
  have h := reflection_log_9524_neg
  have he : Real.log (455716302047 / 250000000000) = -Real.log (250000000000 / 455716302047) := by
    rw [show ((455716302047 / 250000000000) : ℝ) = ((250000000000 / 455716302047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9525_neg : (51238281 / 200000000) ≤ -Real.log (250 / 323) ∧
    -Real.log (250 / 323) ≤ (128095703 / 500000000) := by
  have h := checkLog_sound (w := (73 / 573)) (n := 12)
    (lo := (51238281 / 200000000)) (hi := (128095703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323 / 250) = 1/(250 / 323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9525 : Bounds (51238281 / 200000000) (128095703 / 500000000) (Real.log (323 / 250)) := by
  have h := reflection_log_9525_neg
  have he : Real.log (323 / 250) = -Real.log (250 / 323) := by
    rw [show ((323 / 250) : ℝ) = ((250 / 323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9526_neg : (69062237 / 200000000) ≤ -Real.log (177 / 250) ∧
    -Real.log (177 / 250) ≤ (172655593 / 500000000) := by
  have h := checkLog_sound (w := (73 / 427)) (n := 12)
    (lo := (69062237 / 200000000)) (hi := (172655593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 177) = 1/(177 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9526 : Bounds (-172655593 / 500000000) (-69062237 / 200000000) (Real.log (177 / 250)) := by
  have h := reflection_log_9526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9527_neg : (291957 / 1000000000) ≤ -Real.log (250000 / 250073) ∧
    -Real.log (250000 / 250073) ≤ (145979 / 500000000) := by
  have h := checkLog_sound (w := (73 / 500073)) (n := 12)
    (lo := (291957 / 1000000000)) (hi := (145979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250073 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250073 / 250000) = 1/(250000 / 250073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9527 : Bounds (291957 / 1000000000) (145979 / 500000000) (Real.log (250073 / 250000)) := by
  have h := reflection_log_9527_neg
  have he : Real.log (250073 / 250000) = -Real.log (250000 / 250073) := by
    rw [show ((250073 / 250000) : ℝ) = ((250000 / 250073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9528_neg : (146021 / 500000000) ≤ -Real.log (249927 / 250000) ∧
    -Real.log (249927 / 250000) ≤ (292043 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 499927)) (n := 12)
    (lo := (146021 / 500000000)) (hi := (292043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249927) = 1/(249927 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9528 : Bounds (-292043 / 1000000000) (-146021 / 500000000) (Real.log (249927 / 250000)) := by
  have h := reflection_log_9528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9529_neg : (34482893 / 250000000) ≤ -Real.log (1000000 / 1147897) ∧
    -Real.log (1000000 / 1147897) ≤ (137931573 / 1000000000) := by
  have h := checkLog_sound (w := (147897 / 2147897)) (n := 12)
    (lo := (34482893 / 250000000)) (hi := (137931573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147897 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1147897 / 1000000) = 1/(1000000 / 1147897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9529 : Bounds (34482893 / 250000000) (137931573 / 1000000000) (Real.log (1147897 / 1000000)) := by
  have h := reflection_log_9529_neg
  have he : Real.log (1147897 / 1000000) = -Real.log (1000000 / 1147897) := by
    rw [show ((1147897 / 1000000) : ℝ) = ((1000000 / 1147897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9530_neg : (160047867 / 1000000000) ≤ -Real.log (852103 / 1000000) ∧
    -Real.log (852103 / 1000000) ≤ (40011967 / 250000000) := by
  have h := checkLog_sound (w := (147897 / 1852103)) (n := 12)
    (lo := (160047867 / 1000000000)) (hi := (40011967 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 852103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 852103) = 1/(852103 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9530 : Bounds (-40011967 / 250000000) (-160047867 / 1000000000) (Real.log (852103 / 1000000)) := by
  have h := reflection_log_9530_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9531_neg : (69205297 / 500000000) ≤ -Real.log (1000000 / 1148447) ∧
    -Real.log (1000000 / 1148447) ≤ (27682119 / 200000000) := by
  have h := checkLog_sound (w := (148447 / 2148447)) (n := 12)
    (lo := (69205297 / 500000000)) (hi := (27682119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1148447 / 1000000) = 1/(1000000 / 1148447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9531 : Bounds (69205297 / 500000000) (27682119 / 200000000) (Real.log (1148447 / 1000000)) := by
  have h := reflection_log_9531_neg
  have he : Real.log (1148447 / 1000000) = -Real.log (1000000 / 1148447) := by
    rw [show ((1148447 / 1000000) : ℝ) = ((1000000 / 1148447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9532_neg : (160693537 / 1000000000) ≤ -Real.log (851553 / 1000000) ∧
    -Real.log (851553 / 1000000) ≤ (80346769 / 500000000) := by
  have h := checkLog_sound (w := (148447 / 1851553)) (n := 12)
    (lo := (160693537 / 1000000000)) (hi := (80346769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 851553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 851553) = 1/(851553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9532 : Bounds (-80346769 / 500000000) (-160693537 / 1000000000) (Real.log (851553 / 1000000)) := by
  have h := reflection_log_9532_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9533_neg : (11141471 / 500000000) ≤ -Real.log (977963488191 / 1000000000000) ∧
    -Real.log (977963488191 / 1000000000000) ≤ (22282943 / 1000000000) := by
  have h := checkLog_sound (w := (22036511809 / 1977963488191)) (n := 12)
    (lo := (11141471 / 500000000)) (hi := (22282943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977963488191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977963488191) = 1/(977963488191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9533 : Bounds (-22282943 / 1000000000) (-11141471 / 500000000) (Real.log (977963488191 / 1000000000000)) := by
  have h := reflection_log_9533_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9534_neg : (11058147 / 500000000) ≤ -Real.log (978126477391 / 1000000000000) ∧
    -Real.log (978126477391 / 1000000000000) ≤ (4423259 / 200000000) := by
  have h := checkLog_sound (w := (21873522609 / 1978126477391)) (n := 12)
    (lo := (11058147 / 500000000)) (hi := (4423259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978126477391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978126477391) = 1/(978126477391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9534 : Bounds (-4423259 / 200000000) (-11058147 / 500000000) (Real.log (978126477391 / 1000000000000)) := by
  have h := reflection_log_9534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9535_neg : (3724743 / 12500000) ≤ -Real.log (250000000000 / 336783522649) ∧
    -Real.log (250000000000 / 336783522649) ≤ (297979441 / 1000000000) := by
  have h := checkLog_sound (w := (86783522649 / 586783522649)) (n := 12)
    (lo := (3724743 / 12500000)) (hi := (297979441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336783522649 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336783522649 / 250000000000) = 1/(250000000000 / 336783522649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9535 : Bounds (3724743 / 12500000) (297979441 / 1000000000) (Real.log (336783522649 / 250000000000)) := by
  have h := reflection_log_9535_neg
  have he : Real.log (336783522649 / 250000000000) = -Real.log (250000000000 / 336783522649) := by
    rw [show ((336783522649 / 250000000000) : ℝ) = ((250000000000 / 336783522649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
