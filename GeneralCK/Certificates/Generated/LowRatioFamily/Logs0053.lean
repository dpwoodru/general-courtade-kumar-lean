import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3392_neg : (22917827 / 250000000) ≤ -Real.log (182481 / 200000) ∧
    -Real.log (182481 / 200000) ≤ (91671309 / 1000000000) := by
  have h := checkLog_sound (w := (17519 / 382481)) (n := 12)
    (lo := (22917827 / 250000000)) (hi := (91671309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182481) = 1/(182481 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3392 : Bounds (-91671309 / 1000000000) (-22917827 / 250000000) (Real.log (182481 / 200000)) := by
  have h := reflection_log_3392_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3393_neg : (21044153 / 250000000) ≤ -Real.log (1000000 / 1087821) ∧
    -Real.log (1000000 / 1087821) ≤ (84176613 / 1000000000) := by
  have h := checkLog_sound (w := (87821 / 2087821)) (n := 12)
    (lo := (21044153 / 250000000)) (hi := (84176613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087821 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087821 / 1000000) = 1/(1000000 / 1087821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3393 : Bounds (21044153 / 250000000) (84176613 / 1000000000) (Real.log (1087821 / 1000000)) := by
  have h := reflection_log_3393_neg
  have he : Real.log (1087821 / 1000000) = -Real.log (1000000 / 1087821) := by
    rw [show ((1087821 / 1000000) : ℝ) = ((1000000 / 1087821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3394_neg : (22979759 / 250000000) ≤ -Real.log (912179 / 1000000) ∧
    -Real.log (912179 / 1000000) ≤ (91919037 / 1000000000) := by
  have h := checkLog_sound (w := (87821 / 1912179)) (n := 12)
    (lo := (22979759 / 250000000)) (hi := (91919037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912179) = 1/(912179 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3394 : Bounds (-91919037 / 1000000000) (-22979759 / 250000000) (Real.log (912179 / 1000000)) := by
  have h := reflection_log_3394_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3395_neg : (7742423 / 1000000000) ≤ -Real.log (992287471959 / 1000000000000) ∧
    -Real.log (992287471959 / 1000000000000) ≤ (967803 / 125000000) := by
  have h := checkLog_sound (w := (7712528041 / 1992287471959)) (n := 12)
    (lo := (7742423 / 1000000000)) (hi := (967803 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992287471959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992287471959) = 1/(992287471959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3395 : Bounds (-967803 / 125000000) (-7742423 / 1000000000) (Real.log (992287471959 / 1000000000000)) := by
  have h := reflection_log_3395_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3396_neg : (962809 / 125000000) ≤ -Real.log (39693084639 / 40000000000) ∧
    -Real.log (39693084639 / 40000000000) ≤ (7702473 / 1000000000) := by
  have h := checkLog_sound (w := (306915361 / 79693084639)) (n := 12)
    (lo := (962809 / 125000000)) (hi := (7702473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39693084639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39693084639) = 1/(39693084639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3396 : Bounds (-7702473 / 1000000000) (-962809 / 125000000) (Real.log (39693084639 / 40000000000)) := by
  have h := reflection_log_3396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3397_neg : (35128029 / 200000000) ≤ -Real.log (250000000000 / 298002257769) ∧
    -Real.log (250000000000 / 298002257769) ≤ (87820073 / 500000000) := by
  have h := checkLog_sound (w := (48002257769 / 548002257769)) (n := 12)
    (lo := (35128029 / 200000000)) (hi := (87820073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298002257769 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298002257769 / 250000000000) = 1/(250000000000 / 298002257769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3397 : Bounds (35128029 / 200000000) (87820073 / 500000000) (Real.log (298002257769 / 250000000000)) := by
  have h := reflection_log_3397_neg
  have he : Real.log (298002257769 / 250000000000) = -Real.log (250000000000 / 298002257769) := by
    rw [show ((298002257769 / 250000000000) : ℝ) = ((250000000000 / 298002257769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3398_neg : (176095649 / 1000000000) ≤ -Real.log (500000000000 / 596276059853) ∧
    -Real.log (500000000000 / 596276059853) ≤ (3521913 / 20000000) := by
  have h := checkLog_sound (w := (96276059853 / 1096276059853)) (n := 12)
    (lo := (176095649 / 1000000000)) (hi := (3521913 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596276059853 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596276059853 / 500000000000) = 1/(500000000000 / 596276059853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3398 : Bounds (176095649 / 1000000000) (3521913 / 20000000) (Real.log (596276059853 / 500000000000)) := by
  have h := reflection_log_3398_neg
  have he : Real.log (596276059853 / 500000000000) = -Real.log (500000000000 / 596276059853) := by
    rw [show ((596276059853 / 500000000000) : ℝ) = ((500000000000 / 596276059853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3399_neg : (352402263 / 1000000000) ≤ -Real.log (500000000000 / 711240310077) ∧
    -Real.log (500000000000 / 711240310077) ≤ (44050283 / 125000000) := by
  have h := checkLog_sound (w := (211240310077 / 1211240310077)) (n := 12)
    (lo := (352402263 / 1000000000)) (hi := (44050283 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711240310077 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711240310077 / 500000000000) = 1/(500000000000 / 711240310077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3399 : Bounds (352402263 / 1000000000) (44050283 / 125000000) (Real.log (711240310077 / 500000000000)) := by
  have h := reflection_log_3399_neg
  have he : Real.log (711240310077 / 500000000000) = -Real.log (500000000000 / 711240310077) := by
    rw [show ((711240310077 / 500000000000) : ℝ) = ((500000000000 / 711240310077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3400_neg : (17630427 / 50000000) ≤ -Real.log (500000000000 / 711387038159) ∧
    -Real.log (500000000000 / 711387038159) ≤ (352608541 / 1000000000) := by
  have h := checkLog_sound (w := (211387038159 / 1211387038159)) (n := 12)
    (lo := (17630427 / 50000000)) (hi := (352608541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711387038159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711387038159 / 500000000000) = 1/(500000000000 / 711387038159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3400 : Bounds (17630427 / 50000000) (352608541 / 1000000000) (Real.log (711387038159 / 500000000000)) := by
  have h := reflection_log_3400_neg
  have he : Real.log (711387038159 / 500000000000) = -Real.log (500000000000 / 711387038159) := by
    rw [show ((711387038159 / 500000000000) : ℝ) = ((500000000000 / 711387038159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3401_neg : (10057979 / 62500000) ≤ -Real.log (5000 / 5873) ∧
    -Real.log (5000 / 5873) ≤ (32185533 / 200000000) := by
  have h := checkLog_sound (w := (873 / 10873)) (n := 12)
    (lo := (10057979 / 62500000)) (hi := (32185533 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5873 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5873 / 5000) = 1/(5000 / 5873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3401 : Bounds (10057979 / 62500000) (32185533 / 200000000) (Real.log (5873 / 5000)) := by
  have h := reflection_log_3401_neg
  have he : Real.log (5873 / 5000) = -Real.log (5000 / 5873) := by
    rw [show ((5873 / 5000) : ℝ) = ((5000 / 5873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3402_neg : (191887161 / 1000000000) ≤ -Real.log (4127 / 5000) ∧
    -Real.log (4127 / 5000) ≤ (95943581 / 500000000) := by
  have h := checkLog_sound (w := (873 / 9127)) (n := 12)
    (lo := (191887161 / 1000000000)) (hi := (95943581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4127) = 1/(4127 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3402 : Bounds (-95943581 / 500000000) (-191887161 / 1000000000) (Real.log (4127 / 5000)) := by
  have h := reflection_log_3402_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3403_neg : (21823 / 125000000) ≤ -Real.log (5000000 / 5000873) ∧
    -Real.log (5000000 / 5000873) ≤ (34917 / 200000000) := by
  have h := checkLog_sound (w := (873 / 10000873)) (n := 12)
    (lo := (21823 / 125000000)) (hi := (34917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000873 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000873 / 5000000) = 1/(5000000 / 5000873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3403 : Bounds (21823 / 125000000) (34917 / 200000000) (Real.log (5000873 / 5000000)) := by
  have h := reflection_log_3403_neg
  have he : Real.log (5000873 / 5000000) = -Real.log (5000000 / 5000873) := by
    rw [show ((5000873 / 5000000) : ℝ) = ((5000000 / 5000873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3404_neg : (34923 / 200000000) ≤ -Real.log (4999127 / 5000000) ∧
    -Real.log (4999127 / 5000000) ≤ (21827 / 125000000) := by
  have h := checkLog_sound (w := (873 / 9999127)) (n := 12)
    (lo := (34923 / 200000000)) (hi := (21827 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999127) = 1/(4999127 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3404 : Bounds (-21827 / 125000000) (-34923 / 200000000) (Real.log (4999127 / 5000000)) := by
  have h := reflection_log_3404_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3405_neg : (84015727 / 1000000000) ≤ -Real.log (500000 / 543823) ∧
    -Real.log (500000 / 543823) ≤ (5250983 / 62500000) := by
  have h := checkLog_sound (w := (43823 / 1043823)) (n := 12)
    (lo := (84015727 / 1000000000)) (hi := (5250983 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543823 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543823 / 500000) = 1/(500000 / 543823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3405 : Bounds (84015727 / 1000000000) (5250983 / 62500000) (Real.log (543823 / 500000)) := by
  have h := reflection_log_3405_neg
  have he : Real.log (543823 / 500000) = -Real.log (500000 / 543823) := by
    rw [show ((543823 / 500000) : ℝ) = ((500000 / 543823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3406_neg : (45863603 / 500000000) ≤ -Real.log (456177 / 500000) ∧
    -Real.log (456177 / 500000) ≤ (91727207 / 1000000000) := by
  have h := checkLog_sound (w := (43823 / 956177)) (n := 12)
    (lo := (45863603 / 500000000)) (hi := (91727207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456177) = 1/(456177 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3406 : Bounds (-91727207 / 1000000000) (-45863603 / 500000000) (Real.log (456177 / 500000)) := by
  have h := reflection_log_3406_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3407_neg : (42111747 / 500000000) ≤ -Real.log (15625 / 16998) ∧
    -Real.log (15625 / 16998) ≤ (16844699 / 200000000) := by
  have h := checkLog_sound (w := (1373 / 32623)) (n := 12)
    (lo := (42111747 / 500000000)) (hi := (16844699 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16998 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16998 / 15625) = 1/(15625 / 16998) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3407 : Bounds (42111747 / 500000000) (16844699 / 200000000) (Real.log (16998 / 15625)) := by
  have h := reflection_log_3407_neg
  have he : Real.log (16998 / 15625) = -Real.log (15625 / 16998) := by
    rw [show ((16998 / 15625) : ℝ) = ((15625 / 16998) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3408_neg : (91974947 / 1000000000) ≤ -Real.log (14252 / 15625) ∧
    -Real.log (14252 / 15625) ≤ (22993737 / 250000000) := by
  have h := checkLog_sound (w := (1373 / 29877)) (n := 12)
    (lo := (91974947 / 1000000000)) (hi := (22993737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14252) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14252) = 1/(14252 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3408 : Bounds (-22993737 / 250000000) (-91974947 / 1000000000) (Real.log (14252 / 15625)) := by
  have h := reflection_log_3408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3409_neg : (7751453 / 1000000000) ≤ -Real.log (242255496 / 244140625) ∧
    -Real.log (242255496 / 244140625) ≤ (3875727 / 500000000) := by
  have h := checkLog_sound (w := (1885129 / 486396121)) (n := 12)
    (lo := (7751453 / 1000000000)) (hi := (3875727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242255496) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242255496) = 1/(242255496 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3409 : Bounds (-3875727 / 500000000) (-7751453 / 1000000000) (Real.log (242255496 / 244140625)) := by
  have h := reflection_log_3409_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3410_neg : (3855739 / 500000000) ≤ -Real.log (248079544671 / 250000000000) ∧
    -Real.log (248079544671 / 250000000000) ≤ (7711479 / 1000000000) := by
  have h := checkLog_sound (w := (1920455329 / 498079544671)) (n := 12)
    (lo := (3855739 / 500000000)) (hi := (7711479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248079544671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248079544671) = 1/(248079544671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3410 : Bounds (-7711479 / 1000000000) (-3855739 / 500000000) (Real.log (248079544671 / 250000000000)) := by
  have h := reflection_log_3410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3411_neg : (87871467 / 500000000) ≤ -Real.log (500000000000 / 596065781483) ∧
    -Real.log (500000000000 / 596065781483) ≤ (35148587 / 200000000) := by
  have h := checkLog_sound (w := (96065781483 / 1096065781483)) (n := 12)
    (lo := (87871467 / 500000000)) (hi := (35148587 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596065781483 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596065781483 / 500000000000) = 1/(500000000000 / 596065781483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3411 : Bounds (87871467 / 500000000) (35148587 / 200000000) (Real.log (596065781483 / 500000000000)) := by
  have h := reflection_log_3411_neg
  have he : Real.log (596065781483 / 500000000000) = -Real.log (500000000000 / 596065781483) := by
    rw [show ((596065781483 / 500000000000) : ℝ) = ((500000000000 / 596065781483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3412_neg : (88099221 / 500000000) ≤ -Real.log (500000000000 / 596337356161) ∧
    -Real.log (500000000000 / 596337356161) ≤ (176198443 / 1000000000) := by
  have h := checkLog_sound (w := (96337356161 / 1096337356161)) (n := 12)
    (lo := (88099221 / 500000000)) (hi := (176198443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596337356161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596337356161 / 500000000000) = 1/(500000000000 / 596337356161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3412 : Bounds (88099221 / 500000000) (176198443 / 1000000000) (Real.log (596337356161 / 500000000000)) := by
  have h := reflection_log_3412_neg
  have he : Real.log (596337356161 / 500000000000) = -Real.log (500000000000 / 596337356161) := by
    rw [show ((596337356161 / 500000000000) : ℝ) = ((500000000000 / 596337356161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3413_neg : (17630427 / 50000000) ≤ -Real.log (250000000000 / 355693519079) ∧
    -Real.log (250000000000 / 355693519079) ≤ (352608541 / 1000000000) := by
  have h := checkLog_sound (w := (105693519079 / 605693519079)) (n := 12)
    (lo := (17630427 / 50000000)) (hi := (352608541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355693519079 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355693519079 / 250000000000) = 1/(250000000000 / 355693519079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3413 : Bounds (17630427 / 50000000) (352608541 / 1000000000) (Real.log (355693519079 / 250000000000)) := by
  have h := reflection_log_3413_neg
  have he : Real.log (355693519079 / 250000000000) = -Real.log (250000000000 / 355693519079) := by
    rw [show ((355693519079 / 250000000000) : ℝ) = ((250000000000 / 355693519079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3414_neg : (14112593 / 40000000) ≤ -Real.log (250000000000 / 355766900897) ∧
    -Real.log (250000000000 / 355766900897) ≤ (176407413 / 500000000) := by
  have h := checkLog_sound (w := (105766900897 / 605766900897)) (n := 12)
    (lo := (14112593 / 40000000)) (hi := (176407413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355766900897 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355766900897 / 250000000000) = 1/(250000000000 / 355766900897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3414 : Bounds (14112593 / 40000000) (176407413 / 500000000) (Real.log (355766900897 / 250000000000)) := by
  have h := reflection_log_3414_neg
  have he : Real.log (355766900897 / 250000000000) = -Real.log (250000000000 / 355766900897) := by
    rw [show ((355766900897 / 250000000000) : ℝ) = ((250000000000 / 355766900897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3415_neg : (32202559 / 200000000) ≤ -Real.log (10000 / 11747) ∧
    -Real.log (10000 / 11747) ≤ (40253199 / 250000000) := by
  have h := checkLog_sound (w := (1747 / 21747)) (n := 12)
    (lo := (32202559 / 200000000)) (hi := (40253199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11747 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11747 / 10000) = 1/(10000 / 11747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3415 : Bounds (32202559 / 200000000) (40253199 / 250000000) (Real.log (11747 / 10000)) := by
  have h := reflection_log_3415_neg
  have he : Real.log (11747 / 10000) = -Real.log (10000 / 11747) := by
    rw [show ((11747 / 10000) : ℝ) = ((10000 / 11747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3416_neg : (96004161 / 500000000) ≤ -Real.log (8253 / 10000) ∧
    -Real.log (8253 / 10000) ≤ (192008323 / 1000000000) := by
  have h := checkLog_sound (w := (1747 / 18253)) (n := 12)
    (lo := (96004161 / 500000000)) (hi := (192008323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8253) = 1/(8253 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3416 : Bounds (-192008323 / 1000000000) (-96004161 / 500000000) (Real.log (8253 / 10000)) := by
  have h := reflection_log_3416_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3417_neg : (43671 / 250000000) ≤ -Real.log (10000000 / 10001747) ∧
    -Real.log (10000000 / 10001747) ≤ (34937 / 200000000) := by
  have h := checkLog_sound (w := (1747 / 20001747)) (n := 12)
    (lo := (43671 / 250000000)) (hi := (34937 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001747 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001747 / 10000000) = 1/(10000000 / 10001747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3417 : Bounds (43671 / 250000000) (34937 / 200000000) (Real.log (10001747 / 10000000)) := by
  have h := reflection_log_3417_neg
  have he : Real.log (10001747 / 10000000) = -Real.log (10000000 / 10001747) := by
    rw [show ((10001747 / 10000000) : ℝ) = ((10000000 / 10001747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3418_neg : (34943 / 200000000) ≤ -Real.log (9998253 / 10000000) ∧
    -Real.log (9998253 / 10000000) ≤ (43679 / 250000000) := by
  have h := checkLog_sound (w := (1747 / 19998253)) (n := 12)
    (lo := (34943 / 200000000)) (hi := (43679 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998253) = 1/(9998253 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3418 : Bounds (-43679 / 250000000) (-34943 / 200000000) (Real.log (9998253 / 10000000)) := by
  have h := reflection_log_3418_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3419_neg : (84062617 / 1000000000) ≤ -Real.log (1000000 / 1087697) ∧
    -Real.log (1000000 / 1087697) ≤ (42031309 / 500000000) := by
  have h := checkLog_sound (w := (87697 / 2087697)) (n := 12)
    (lo := (84062617 / 1000000000)) (hi := (42031309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087697 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087697 / 1000000) = 1/(1000000 / 1087697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3419 : Bounds (84062617 / 1000000000) (42031309 / 500000000) (Real.log (1087697 / 1000000)) := by
  have h := reflection_log_3419_neg
  have he : Real.log (1087697 / 1000000) = -Real.log (1000000 / 1087697) := by
    rw [show ((1087697 / 1000000) : ℝ) = ((1000000 / 1087697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3420_neg : (91783107 / 1000000000) ≤ -Real.log (912303 / 1000000) ∧
    -Real.log (912303 / 1000000) ≤ (22945777 / 250000000) := by
  have h := checkLog_sound (w := (87697 / 1912303)) (n := 12)
    (lo := (91783107 / 1000000000)) (hi := (22945777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912303) = 1/(912303 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3420 : Bounds (-22945777 / 250000000) (-91783107 / 1000000000) (Real.log (912303 / 1000000)) := by
  have h := reflection_log_3420_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3421_neg : (42134727 / 500000000) ≤ -Real.log (500000 / 543961) ∧
    -Real.log (500000 / 543961) ≤ (16853891 / 200000000) := by
  have h := checkLog_sound (w := (43961 / 1043961)) (n := 12)
    (lo := (42134727 / 500000000)) (hi := (16853891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543961 / 500000) = 1/(500000 / 543961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3421 : Bounds (42134727 / 500000000) (16853891 / 200000000) (Real.log (543961 / 500000)) := by
  have h := reflection_log_3421_neg
  have he : Real.log (543961 / 500000) = -Real.log (500000 / 543961) := by
    rw [show ((543961 / 500000) : ℝ) = ((500000 / 543961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3422_neg : (46014883 / 500000000) ≤ -Real.log (456039 / 500000) ∧
    -Real.log (456039 / 500000) ≤ (92029767 / 1000000000) := by
  have h := checkLog_sound (w := (43961 / 956039)) (n := 12)
    (lo := (46014883 / 500000000)) (hi := (92029767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456039) = 1/(456039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3422 : Bounds (-92029767 / 1000000000) (-46014883 / 500000000) (Real.log (456039 / 500000)) := by
  have h := reflection_log_3422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3423_neg : (7760311 / 1000000000) ≤ -Real.log (248067430479 / 250000000000) ∧
    -Real.log (248067430479 / 250000000000) ≤ (970039 / 125000000) := by
  have h := checkLog_sound (w := (1932569521 / 498067430479)) (n := 12)
    (lo := (7760311 / 1000000000)) (hi := (970039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248067430479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248067430479) = 1/(248067430479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3423 : Bounds (-970039 / 125000000) (-7760311 / 1000000000) (Real.log (248067430479 / 250000000000)) := by
  have h := reflection_log_3423_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3424_neg : (772049 / 100000000) ≤ -Real.log (992309236191 / 1000000000000) ∧
    -Real.log (992309236191 / 1000000000000) ≤ (7720491 / 1000000000) := by
  have h := checkLog_sound (w := (7690763809 / 1992309236191)) (n := 12)
    (lo := (772049 / 100000000)) (hi := (7720491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992309236191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992309236191) = 1/(992309236191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3424 : Bounds (-7720491 / 1000000000) (-772049 / 100000000) (Real.log (992309236191 / 1000000000000)) := by
  have h := reflection_log_3424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3425_neg : (43961431 / 250000000) ≤ -Real.log (500000000000 / 596127054279) ∧
    -Real.log (500000000000 / 596127054279) ≤ (7033829 / 40000000) := by
  have h := checkLog_sound (w := (96127054279 / 1096127054279)) (n := 12)
    (lo := (43961431 / 250000000)) (hi := (7033829 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596127054279 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596127054279 / 500000000000) = 1/(500000000000 / 596127054279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3425 : Bounds (43961431 / 250000000) (7033829 / 40000000) (Real.log (596127054279 / 500000000000)) := by
  have h := reflection_log_3425_neg
  have he : Real.log (596127054279 / 500000000000) = -Real.log (500000000000 / 596127054279) := by
    rw [show ((596127054279 / 500000000000) : ℝ) = ((500000000000 / 596127054279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3426_neg : (8814961 / 50000000) ≤ -Real.log (125000000000 / 149099364309) ∧
    -Real.log (125000000000 / 149099364309) ≤ (176299221 / 1000000000) := by
  have h := checkLog_sound (w := (24099364309 / 274099364309)) (n := 12)
    (lo := (8814961 / 50000000)) (hi := (176299221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149099364309 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149099364309 / 125000000000) = 1/(125000000000 / 149099364309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3426 : Bounds (8814961 / 50000000) (176299221 / 1000000000) (Real.log (149099364309 / 125000000000)) := by
  have h := reflection_log_3426_neg
  have he : Real.log (149099364309 / 125000000000) = -Real.log (125000000000 / 149099364309) := by
    rw [show ((149099364309 / 125000000000) : ℝ) = ((125000000000 / 149099364309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3427_neg : (14112593 / 40000000) ≤ -Real.log (500000000000 / 711533801793) ∧
    -Real.log (500000000000 / 711533801793) ≤ (176407413 / 500000000) := by
  have h := checkLog_sound (w := (211533801793 / 1211533801793)) (n := 12)
    (lo := (14112593 / 40000000)) (hi := (176407413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711533801793 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711533801793 / 500000000000) = 1/(500000000000 / 711533801793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3427 : Bounds (14112593 / 40000000) (176407413 / 500000000) (Real.log (711533801793 / 500000000000)) := by
  have h := reflection_log_3427_neg
  have he : Real.log (711533801793 / 500000000000) = -Real.log (500000000000 / 711533801793) := by
    rw [show ((711533801793 / 500000000000) : ℝ) = ((500000000000 / 711533801793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3428_neg : (176510559 / 500000000) ≤ -Real.log (250000000000 / 355840300497) ∧
    -Real.log (250000000000 / 355840300497) ≤ (353021119 / 1000000000) := by
  have h := checkLog_sound (w := (105840300497 / 605840300497)) (n := 12)
    (lo := (176510559 / 500000000)) (hi := (353021119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355840300497 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355840300497 / 250000000000) = 1/(250000000000 / 355840300497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3428 : Bounds (176510559 / 500000000) (353021119 / 1000000000) (Real.log (355840300497 / 250000000000)) := by
  have h := reflection_log_3428_neg
  have he : Real.log (355840300497 / 250000000000) = -Real.log (250000000000 / 355840300497) := by
    rw [show ((355840300497 / 250000000000) : ℝ) = ((250000000000 / 355840300497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3429_neg : (503431 / 3125000) ≤ -Real.log (2500 / 2937) ∧
    -Real.log (2500 / 2937) ≤ (161097921 / 1000000000) := by
  have h := checkLog_sound (w := (437 / 5437)) (n := 12)
    (lo := (503431 / 3125000)) (hi := (161097921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2937 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2937 / 2500) = 1/(2500 / 2937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3429 : Bounds (503431 / 3125000) (161097921 / 1000000000) (Real.log (2937 / 2500)) := by
  have h := reflection_log_3429_neg
  have he : Real.log (2937 / 2500) = -Real.log (2500 / 2937) := by
    rw [show ((2937 / 2500) : ℝ) = ((2500 / 2937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3430_neg : (192129497 / 1000000000) ≤ -Real.log (2063 / 2500) ∧
    -Real.log (2063 / 2500) ≤ (96064749 / 500000000) := by
  have h := checkLog_sound (w := (437 / 4563)) (n := 12)
    (lo := (192129497 / 1000000000)) (hi := (96064749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2063) = 1/(2063 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3430 : Bounds (-96064749 / 500000000) (-192129497 / 1000000000) (Real.log (2063 / 2500)) := by
  have h := reflection_log_3430_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3431_neg : (2731 / 15625000) ≤ -Real.log (2500000 / 2500437) ∧
    -Real.log (2500000 / 2500437) ≤ (34957 / 200000000) := by
  have h := checkLog_sound (w := (437 / 5000437)) (n := 12)
    (lo := (2731 / 15625000)) (hi := (34957 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500437 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500437 / 2500000) = 1/(2500000 / 2500437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3431 : Bounds (2731 / 15625000) (34957 / 200000000) (Real.log (2500437 / 2500000)) := by
  have h := reflection_log_3431_neg
  have he : Real.log (2500437 / 2500000) = -Real.log (2500000 / 2500437) := by
    rw [show ((2500437 / 2500000) : ℝ) = ((2500000 / 2500437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3432_neg : (34963 / 200000000) ≤ -Real.log (2499563 / 2500000) ∧
    -Real.log (2499563 / 2500000) ≤ (5463 / 31250000) := by
  have h := checkLog_sound (w := (437 / 4999563)) (n := 12)
    (lo := (34963 / 200000000)) (hi := (5463 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499563) = 1/(2499563 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3432 : Bounds (-5463 / 31250000) (-34963 / 200000000) (Real.log (2499563 / 2500000)) := by
  have h := reflection_log_3432_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3433_neg : (84109503 / 1000000000) ≤ -Real.log (250000 / 271937) ∧
    -Real.log (250000 / 271937) ≤ (1314211 / 15625000) := by
  have h := checkLog_sound (w := (21937 / 521937)) (n := 12)
    (lo := (84109503 / 1000000000)) (hi := (1314211 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271937 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271937 / 250000) = 1/(250000 / 271937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3433 : Bounds (84109503 / 1000000000) (1314211 / 15625000) (Real.log (271937 / 250000)) := by
  have h := reflection_log_3433_neg
  have he : Real.log (271937 / 250000) = -Real.log (250000 / 271937) := by
    rw [show ((271937 / 250000) : ℝ) = ((250000 / 271937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3434_neg : (91839011 / 1000000000) ≤ -Real.log (228063 / 250000) ∧
    -Real.log (228063 / 250000) ≤ (22959753 / 250000000) := by
  have h := checkLog_sound (w := (21937 / 478063)) (n := 12)
    (lo := (91839011 / 1000000000)) (hi := (22959753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228063) = 1/(228063 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3434 : Bounds (-22959753 / 250000000) (-91839011 / 1000000000) (Real.log (228063 / 250000)) := by
  have h := reflection_log_3434_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3435_neg : (84316331 / 1000000000) ≤ -Real.log (1000000 / 1087973) ∧
    -Real.log (1000000 / 1087973) ≤ (21079083 / 250000000) := by
  have h := checkLog_sound (w := (87973 / 2087973)) (n := 12)
    (lo := (84316331 / 1000000000)) (hi := (21079083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087973 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087973 / 1000000) = 1/(1000000 / 1087973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3435 : Bounds (84316331 / 1000000000) (21079083 / 250000000) (Real.log (1087973 / 1000000)) := by
  have h := reflection_log_3435_neg
  have he : Real.log (1087973 / 1000000) = -Real.log (1000000 / 1087973) := by
    rw [show ((1087973 / 1000000) : ℝ) = ((1000000 / 1087973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3436_neg : (23021421 / 250000000) ≤ -Real.log (912027 / 1000000) ∧
    -Real.log (912027 / 1000000) ≤ (18417137 / 200000000) := by
  have h := checkLog_sound (w := (87973 / 1912027)) (n := 12)
    (lo := (23021421 / 250000000)) (hi := (18417137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912027) = 1/(912027 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3436 : Bounds (-18417137 / 200000000) (-23021421 / 250000000) (Real.log (912027 / 1000000)) := by
  have h := reflection_log_3436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3437_neg : (971169 / 125000000) ≤ -Real.log (992260751271 / 1000000000000) ∧
    -Real.log (992260751271 / 1000000000000) ≤ (7769353 / 1000000000) := by
  have h := checkLog_sound (w := (7739248729 / 1992260751271)) (n := 12)
    (lo := (971169 / 125000000)) (hi := (7769353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992260751271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992260751271) = 1/(992260751271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3437 : Bounds (-7769353 / 1000000000) (-971169 / 125000000) (Real.log (992260751271 / 1000000000000)) := by
  have h := reflection_log_3437_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3438_neg : (7729507 / 1000000000) ≤ -Real.log (62018768031 / 62500000000) ∧
    -Real.log (62018768031 / 62500000000) ≤ (1932377 / 250000000) := by
  have h := checkLog_sound (w := (481231969 / 124518768031)) (n := 12)
    (lo := (7729507 / 1000000000)) (hi := (1932377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62018768031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62018768031) = 1/(62018768031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3438 : Bounds (-1932377 / 250000000) (-7729507 / 1000000000) (Real.log (62018768031 / 62500000000)) := by
  have h := reflection_log_3438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3439_neg : (35189703 / 200000000) ≤ -Real.log (20000000000 / 23847533357) ∧
    -Real.log (20000000000 / 23847533357) ≤ (43987129 / 250000000) := by
  have h := checkLog_sound (w := (3847533357 / 43847533357)) (n := 12)
    (lo := (35189703 / 200000000)) (hi := (43987129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23847533357 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23847533357 / 20000000000) = 1/(20000000000 / 23847533357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3439 : Bounds (35189703 / 200000000) (43987129 / 250000000) (Real.log (23847533357 / 20000000000)) := by
  have h := reflection_log_3439_neg
  have he : Real.log (23847533357 / 20000000000) = -Real.log (20000000000 / 23847533357) := by
    rw [show ((23847533357 / 20000000000) : ℝ) = ((20000000000 / 23847533357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3440_neg : (5512563 / 31250000) ≤ -Real.log (6250000000 / 7455734589) ∧
    -Real.log (6250000000 / 7455734589) ≤ (176402017 / 1000000000) := by
  have h := checkLog_sound (w := (1205734589 / 13705734589)) (n := 12)
    (lo := (5512563 / 31250000)) (hi := (176402017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7455734589 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7455734589 / 6250000000) = 1/(6250000000 / 7455734589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3440 : Bounds (5512563 / 31250000) (176402017 / 1000000000) (Real.log (7455734589 / 6250000000)) := by
  have h := reflection_log_3440_neg
  have he : Real.log (7455734589 / 6250000000) = -Real.log (6250000000 / 7455734589) := by
    rw [show ((7455734589 / 6250000000) : ℝ) = ((6250000000 / 7455734589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3441_neg : (176510559 / 500000000) ≤ -Real.log (500000000000 / 711680600993) ∧
    -Real.log (500000000000 / 711680600993) ≤ (353021119 / 1000000000) := by
  have h := checkLog_sound (w := (211680600993 / 1211680600993)) (n := 12)
    (lo := (176510559 / 500000000)) (hi := (353021119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711680600993 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711680600993 / 500000000000) = 1/(500000000000 / 711680600993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3441 : Bounds (176510559 / 500000000) (353021119 / 1000000000) (Real.log (711680600993 / 500000000000)) := by
  have h := reflection_log_3441_neg
  have he : Real.log (711680600993 / 500000000000) = -Real.log (500000000000 / 711680600993) := by
    rw [show ((711680600993 / 500000000000) : ℝ) = ((500000000000 / 711680600993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3442_neg : (176613709 / 500000000) ≤ -Real.log (250000000000 / 355913717887) ∧
    -Real.log (250000000000 / 355913717887) ≤ (353227419 / 1000000000) := by
  have h := checkLog_sound (w := (105913717887 / 605913717887)) (n := 12)
    (lo := (176613709 / 500000000)) (hi := (353227419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355913717887 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355913717887 / 250000000000) = 1/(250000000000 / 355913717887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3442 : Bounds (176613709 / 500000000) (353227419 / 1000000000) (Real.log (355913717887 / 250000000000)) := by
  have h := reflection_log_3442_neg
  have he : Real.log (355913717887 / 250000000000) = -Real.log (250000000000 / 355913717887) := by
    rw [show ((355913717887 / 250000000000) : ℝ) = ((250000000000 / 355913717887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3443_neg : (161183037 / 1000000000) ≤ -Real.log (10000 / 11749) ∧
    -Real.log (10000 / 11749) ≤ (80591519 / 500000000) := by
  have h := checkLog_sound (w := (1749 / 21749)) (n := 12)
    (lo := (161183037 / 1000000000)) (hi := (80591519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11749 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11749 / 10000) = 1/(10000 / 11749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3443 : Bounds (161183037 / 1000000000) (80591519 / 500000000) (Real.log (11749 / 10000)) := by
  have h := reflection_log_3443_neg
  have he : Real.log (11749 / 10000) = -Real.log (10000 / 11749) := by
    rw [show ((11749 / 10000) : ℝ) = ((10000 / 11749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3444_neg : (192250687 / 1000000000) ≤ -Real.log (8251 / 10000) ∧
    -Real.log (8251 / 10000) ≤ (3003917 / 15625000) := by
  have h := checkLog_sound (w := (1749 / 18251)) (n := 12)
    (lo := (192250687 / 1000000000)) (hi := (3003917 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8251) = 1/(8251 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3444 : Bounds (-3003917 / 15625000) (-192250687 / 1000000000) (Real.log (8251 / 10000)) := by
  have h := reflection_log_3444_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3445_neg : (43721 / 250000000) ≤ -Real.log (10000000 / 10001749) ∧
    -Real.log (10000000 / 10001749) ≤ (34977 / 200000000) := by
  have h := checkLog_sound (w := (1749 / 20001749)) (n := 12)
    (lo := (43721 / 250000000)) (hi := (34977 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001749 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001749 / 10000000) = 1/(10000000 / 10001749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3445 : Bounds (43721 / 250000000) (34977 / 200000000) (Real.log (10001749 / 10000000)) := by
  have h := reflection_log_3445_neg
  have he : Real.log (10001749 / 10000000) = -Real.log (10000000 / 10001749) := by
    rw [show ((10001749 / 10000000) : ℝ) = ((10000000 / 10001749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3446_neg : (34983 / 200000000) ≤ -Real.log (9998251 / 10000000) ∧
    -Real.log (9998251 / 10000000) ≤ (43729 / 250000000) := by
  have h := checkLog_sound (w := (1749 / 19998251)) (n := 12)
    (lo := (34983 / 200000000)) (hi := (43729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998251) = 1/(9998251 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3446 : Bounds (-43729 / 250000000) (-34983 / 200000000) (Real.log (9998251 / 10000000)) := by
  have h := reflection_log_3446_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3447_neg : (21039097 / 250000000) ≤ -Real.log (1000000 / 1087799) ∧
    -Real.log (1000000 / 1087799) ≤ (84156389 / 1000000000) := by
  have h := checkLog_sound (w := (87799 / 2087799)) (n := 12)
    (lo := (21039097 / 250000000)) (hi := (84156389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087799 / 1000000) = 1/(1000000 / 1087799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3447 : Bounds (21039097 / 250000000) (84156389 / 1000000000) (Real.log (1087799 / 1000000)) := by
  have h := reflection_log_3447_neg
  have he : Real.log (1087799 / 1000000) = -Real.log (1000000 / 1087799) := by
    rw [show ((1087799 / 1000000) : ℝ) = ((1000000 / 1087799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3448_neg : (45947459 / 500000000) ≤ -Real.log (912201 / 1000000) ∧
    -Real.log (912201 / 1000000) ≤ (91894919 / 1000000000) := by
  have h := checkLog_sound (w := (87799 / 1912201)) (n := 12)
    (lo := (45947459 / 500000000)) (hi := (91894919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912201) = 1/(912201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3448 : Bounds (-91894919 / 1000000000) (-45947459 / 500000000) (Real.log (912201 / 1000000)) := by
  have h := reflection_log_3448_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3449_neg : (84363207 / 1000000000) ≤ -Real.log (125000 / 136003) ∧
    -Real.log (125000 / 136003) ≤ (10545401 / 125000000) := by
  have h := checkLog_sound (w := (11003 / 261003)) (n := 12)
    (lo := (84363207 / 1000000000)) (hi := (10545401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136003 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136003 / 125000) = 1/(125000 / 136003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3449 : Bounds (84363207 / 1000000000) (10545401 / 125000000) (Real.log (136003 / 125000)) := by
  have h := reflection_log_3449_neg
  have he : Real.log (136003 / 125000) = -Real.log (125000 / 136003) := by
    rw [show ((136003 / 125000) : ℝ) = ((125000 / 136003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3450_neg : (18428321 / 200000000) ≤ -Real.log (113997 / 125000) ∧
    -Real.log (113997 / 125000) ≤ (46070803 / 500000000) := by
  have h := checkLog_sound (w := (11003 / 238997)) (n := 12)
    (lo := (18428321 / 200000000)) (hi := (46070803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113997) = 1/(113997 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3450 : Bounds (-46070803 / 500000000) (-18428321 / 200000000) (Real.log (113997 / 125000)) := by
  have h := reflection_log_3450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3451_neg : (3889199 / 500000000) ≤ -Real.log (15503933991 / 15625000000) ∧
    -Real.log (15503933991 / 15625000000) ≤ (7778399 / 1000000000) := by
  have h := checkLog_sound (w := (121066009 / 31128933991)) (n := 12)
    (lo := (3889199 / 500000000)) (hi := (7778399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15503933991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15503933991) = 1/(15503933991 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3451 : Bounds (-7778399 / 1000000000) (-3889199 / 500000000) (Real.log (15503933991 / 15625000000)) := by
  have h := reflection_log_3451_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3452_neg : (7738529 / 1000000000) ≤ -Real.log (992291335599 / 1000000000000) ∧
    -Real.log (992291335599 / 1000000000000) ≤ (773853 / 100000000) := by
  have h := checkLog_sound (w := (7708664401 / 1992291335599)) (n := 12)
    (lo := (7738529 / 1000000000)) (hi := (773853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992291335599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992291335599) = 1/(992291335599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3452 : Bounds (-773853 / 100000000) (-7738529 / 1000000000) (Real.log (992291335599 / 1000000000000)) := by
  have h := reflection_log_3452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3453_neg : (176051307 / 1000000000) ≤ -Real.log (500000000000 / 596249620423) ∧
    -Real.log (500000000000 / 596249620423) ≤ (44012827 / 250000000) := by
  have h := checkLog_sound (w := (96249620423 / 1096249620423)) (n := 12)
    (lo := (176051307 / 1000000000)) (hi := (44012827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596249620423 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596249620423 / 500000000000) = 1/(500000000000 / 596249620423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3453 : Bounds (176051307 / 1000000000) (44012827 / 250000000) (Real.log (596249620423 / 500000000000)) := by
  have h := reflection_log_3453_neg
  have he : Real.log (596249620423 / 500000000000) = -Real.log (500000000000 / 596249620423) := by
    rw [show ((596249620423 / 500000000000) : ℝ) = ((500000000000 / 596249620423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3454_neg : (44126203 / 250000000) ≤ -Real.log (250000000000 / 298260041931) ∧
    -Real.log (250000000000 / 298260041931) ≤ (176504813 / 1000000000) := by
  have h := checkLog_sound (w := (48260041931 / 548260041931)) (n := 12)
    (lo := (44126203 / 250000000)) (hi := (176504813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298260041931 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298260041931 / 250000000000) = 1/(250000000000 / 298260041931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3454 : Bounds (44126203 / 250000000) (176504813 / 1000000000) (Real.log (298260041931 / 250000000000)) := by
  have h := reflection_log_3454_neg
  have he : Real.log (298260041931 / 250000000000) = -Real.log (250000000000 / 298260041931) := by
    rw [show ((298260041931 / 250000000000) : ℝ) = ((250000000000 / 298260041931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3455_neg : (176613709 / 500000000) ≤ -Real.log (500000000000 / 711827435773) ∧
    -Real.log (500000000000 / 711827435773) ≤ (353227419 / 1000000000) := by
  have h := checkLog_sound (w := (211827435773 / 1211827435773)) (n := 12)
    (lo := (176613709 / 500000000)) (hi := (353227419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711827435773 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711827435773 / 500000000000) = 1/(500000000000 / 711827435773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3455 : Bounds (176613709 / 500000000) (353227419 / 1000000000) (Real.log (711827435773 / 500000000000)) := by
  have h := reflection_log_3455_neg
  have he : Real.log (711827435773 / 500000000000) = -Real.log (500000000000 / 711827435773) := by
    rw [show ((711827435773 / 500000000000) : ℝ) = ((500000000000 / 711827435773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
