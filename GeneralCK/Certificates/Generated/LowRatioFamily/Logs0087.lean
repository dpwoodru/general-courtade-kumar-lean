import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5568_neg : (96116713 / 250000000) ≤ -Real.log (250000000000 / 367207752129) ∧
    -Real.log (250000000000 / 367207752129) ≤ (384466853 / 1000000000) := by
  have h := checkLog_sound (w := (117207752129 / 617207752129)) (n := 12)
    (lo := (96116713 / 250000000)) (hi := (384466853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367207752129 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367207752129 / 250000000000) = 1/(250000000000 / 367207752129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5568 : Bounds (96116713 / 250000000) (384466853 / 1000000000) (Real.log (367207752129 / 250000000000)) := by
  have h := reflection_log_5568_neg
  have he : Real.log (367207752129 / 250000000000) = -Real.log (250000000000 / 367207752129) := by
    rw [show ((367207752129 / 250000000000) : ℝ) = ((250000000000 / 367207752129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5569_neg : (192337169 / 500000000) ≤ -Real.log (100000000000 / 146913580247) ∧
    -Real.log (100000000000 / 146913580247) ≤ (384674339 / 1000000000) := by
  have h := checkLog_sound (w := (46913580247 / 246913580247)) (n := 12)
    (lo := (192337169 / 500000000)) (hi := (384674339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146913580247 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146913580247 / 100000000000) = 1/(100000000000 / 146913580247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5569 : Bounds (192337169 / 500000000) (384674339 / 1000000000) (Real.log (146913580247 / 100000000000)) := by
  have h := reflection_log_5569_neg
  have he : Real.log (146913580247 / 100000000000) = -Real.log (100000000000 / 146913580247) := by
    rw [show ((146913580247 / 100000000000) : ℝ) = ((100000000000 / 146913580247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5570_neg : (174037337 / 1000000000) ≤ -Real.log (10000 / 11901) ∧
    -Real.log (10000 / 11901) ≤ (87018669 / 500000000) := by
  have h := checkLog_sound (w := (1901 / 21901)) (n := 12)
    (lo := (174037337 / 1000000000)) (hi := (87018669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11901 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11901 / 10000) = 1/(10000 / 11901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5570 : Bounds (174037337 / 1000000000) (87018669 / 500000000) (Real.log (11901 / 10000)) := by
  have h := reflection_log_5570_neg
  have he : Real.log (11901 / 10000) = -Real.log (10000 / 11901) := by
    rw [show ((11901 / 10000) : ℝ) = ((10000 / 11901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5571_neg : (42168899 / 200000000) ≤ -Real.log (8099 / 10000) ∧
    -Real.log (8099 / 10000) ≤ (13177781 / 62500000) := by
  have h := checkLog_sound (w := (1901 / 18099)) (n := 12)
    (lo := (42168899 / 200000000)) (hi := (13177781 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8099) = 1/(8099 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5571 : Bounds (-13177781 / 62500000) (-42168899 / 200000000) (Real.log (8099 / 10000)) := by
  have h := reflection_log_5571_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5572_neg : (190081 / 1000000000) ≤ -Real.log (10000000 / 10001901) ∧
    -Real.log (10000000 / 10001901) ≤ (95041 / 500000000) := by
  have h := checkLog_sound (w := (1901 / 20001901)) (n := 12)
    (lo := (190081 / 1000000000)) (hi := (95041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001901 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001901 / 10000000) = 1/(10000000 / 10001901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5572 : Bounds (190081 / 1000000000) (95041 / 500000000) (Real.log (10001901 / 10000000)) := by
  have h := reflection_log_5572_neg
  have he : Real.log (10001901 / 10000000) = -Real.log (10000000 / 10001901) := by
    rw [show ((10001901 / 10000000) : ℝ) = ((10000000 / 10001901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5573_neg : (95059 / 500000000) ≤ -Real.log (9998099 / 10000000) ∧
    -Real.log (9998099 / 10000000) ≤ (190119 / 1000000000) := by
  have h := checkLog_sound (w := (1901 / 19998099)) (n := 12)
    (lo := (95059 / 500000000)) (hi := (190119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998099) = 1/(9998099 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5573 : Bounds (-190119 / 1000000000) (-95059 / 500000000) (Real.log (9998099 / 10000000)) := by
  have h := reflection_log_5573_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5574_neg : (11404783 / 125000000) ≤ -Real.log (100000 / 109553) ∧
    -Real.log (100000 / 109553) ≤ (18247653 / 200000000) := by
  have h := checkLog_sound (w := (9553 / 209553)) (n := 12)
    (lo := (11404783 / 125000000)) (hi := (18247653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109553 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109553 / 100000) = 1/(100000 / 109553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5574 : Bounds (11404783 / 125000000) (18247653 / 200000000) (Real.log (109553 / 100000)) := by
  have h := reflection_log_5574_neg
  have he : Real.log (109553 / 100000) = -Real.log (100000 / 109553) := by
    rw [show ((109553 / 100000) : ℝ) = ((100000 / 109553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5575_neg : (50203071 / 500000000) ≤ -Real.log (90447 / 100000) ∧
    -Real.log (90447 / 100000) ≤ (100406143 / 1000000000) := by
  have h := checkLog_sound (w := (9553 / 190447)) (n := 12)
    (lo := (50203071 / 500000000)) (hi := (100406143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90447) = 1/(90447 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5575 : Bounds (-100406143 / 1000000000) (-50203071 / 500000000) (Real.log (90447 / 100000)) := by
  have h := reflection_log_5575_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5576_neg : (3658329 / 40000000) ≤ -Real.log (1000000 / 1095771) ∧
    -Real.log (1000000 / 1095771) ≤ (45729113 / 500000000) := by
  have h := checkLog_sound (w := (95771 / 2095771)) (n := 12)
    (lo := (3658329 / 40000000)) (hi := (45729113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095771 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095771 / 1000000) = 1/(1000000 / 1095771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5576 : Bounds (3658329 / 40000000) (45729113 / 500000000) (Real.log (1095771 / 1000000)) := by
  have h := reflection_log_5576_neg
  have he : Real.log (1095771 / 1000000) = -Real.log (1000000 / 1095771) := by
    rw [show ((1095771 / 1000000) : ℝ) = ((1000000 / 1095771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5577_neg : (12584079 / 125000000) ≤ -Real.log (904229 / 1000000) ∧
    -Real.log (904229 / 1000000) ≤ (100672633 / 1000000000) := by
  have h := checkLog_sound (w := (95771 / 1904229)) (n := 12)
    (lo := (12584079 / 125000000)) (hi := (100672633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904229) = 1/(904229 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5577 : Bounds (-100672633 / 1000000000) (-12584079 / 125000000) (Real.log (904229 / 1000000)) := by
  have h := reflection_log_5577_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5578_neg : (4607203 / 500000000) ≤ -Real.log (990827915559 / 1000000000000) ∧
    -Real.log (990827915559 / 1000000000000) ≤ (9214407 / 1000000000) := by
  have h := checkLog_sound (w := (9172084441 / 1990827915559)) (n := 12)
    (lo := (4607203 / 500000000)) (hi := (9214407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990827915559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990827915559) = 1/(990827915559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5578 : Bounds (-9214407 / 1000000000) (-4607203 / 500000000) (Real.log (990827915559 / 1000000000000)) := by
  have h := reflection_log_5578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5579_neg : (9167877 / 1000000000) ≤ -Real.log (9908740191 / 10000000000) ∧
    -Real.log (9908740191 / 10000000000) ≤ (4583939 / 500000000) := by
  have h := checkLog_sound (w := (91259809 / 19908740191)) (n := 12)
    (lo := (9167877 / 1000000000)) (hi := (4583939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9908740191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9908740191) = 1/(9908740191 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5579 : Bounds (-4583939 / 500000000) (-9167877 / 1000000000) (Real.log (9908740191 / 10000000000)) := by
  have h := reflection_log_5579_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5580_neg : (95822203 / 500000000) ≤ -Real.log (500000000000 / 605619865777) ∧
    -Real.log (500000000000 / 605619865777) ≤ (191644407 / 1000000000) := by
  have h := checkLog_sound (w := (105619865777 / 1105619865777)) (n := 12)
    (lo := (95822203 / 500000000)) (hi := (191644407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605619865777 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605619865777 / 500000000000) = 1/(500000000000 / 605619865777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5580 : Bounds (95822203 / 500000000) (191644407 / 1000000000) (Real.log (605619865777 / 500000000000)) := by
  have h := reflection_log_5580_neg
  have he : Real.log (605619865777 / 500000000000) = -Real.log (500000000000 / 605619865777) := by
    rw [show ((605619865777 / 500000000000) : ℝ) = ((500000000000 / 605619865777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5581_neg : (192130857 / 1000000000) ≤ -Real.log (12500000000 / 15147863539) ∧
    -Real.log (12500000000 / 15147863539) ≤ (96065429 / 500000000) := by
  have h := checkLog_sound (w := (2647863539 / 27647863539)) (n := 12)
    (lo := (192130857 / 1000000000)) (hi := (96065429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15147863539 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15147863539 / 12500000000) = 1/(12500000000 / 15147863539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5581 : Bounds (192130857 / 1000000000) (96065429 / 500000000) (Real.log (15147863539 / 12500000000)) := by
  have h := reflection_log_5581_neg
  have he : Real.log (15147863539 / 12500000000) = -Real.log (12500000000 / 15147863539) := by
    rw [show ((15147863539 / 12500000000) : ℝ) = ((12500000000 / 15147863539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5582_neg : (192337169 / 500000000) ≤ -Real.log (250000000000 / 367283950617) ∧
    -Real.log (250000000000 / 367283950617) ≤ (384674339 / 1000000000) := by
  have h := checkLog_sound (w := (117283950617 / 617283950617)) (n := 12)
    (lo := (192337169 / 500000000)) (hi := (384674339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367283950617 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367283950617 / 250000000000) = 1/(250000000000 / 367283950617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5582 : Bounds (192337169 / 500000000) (384674339 / 1000000000) (Real.log (367283950617 / 250000000000)) := by
  have h := reflection_log_5582_neg
  have he : Real.log (367283950617 / 250000000000) = -Real.log (250000000000 / 367283950617) := by
    rw [show ((367283950617 / 250000000000) : ℝ) = ((250000000000 / 367283950617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5583_neg : (48110229 / 125000000) ≤ -Real.log (125000000000 / 183680083961) ∧
    -Real.log (125000000000 / 183680083961) ≤ (384881833 / 1000000000) := by
  have h := checkLog_sound (w := (58680083961 / 308680083961)) (n := 12)
    (lo := (48110229 / 125000000)) (hi := (384881833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183680083961 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183680083961 / 125000000000) = 1/(125000000000 / 183680083961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5583 : Bounds (48110229 / 125000000) (384881833 / 1000000000) (Real.log (183680083961 / 125000000000)) := by
  have h := reflection_log_5583_neg
  have he : Real.log (183680083961 / 125000000000) = -Real.log (125000000000 / 183680083961) := by
    rw [show ((183680083961 / 125000000000) : ℝ) = ((125000000000 / 183680083961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5584_neg : (2176517 / 12500000) ≤ -Real.log (5000 / 5951) ∧
    -Real.log (5000 / 5951) ≤ (174121361 / 1000000000) := by
  have h := checkLog_sound (w := (951 / 10951)) (n := 12)
    (lo := (2176517 / 12500000)) (hi := (174121361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5951 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5951 / 5000) = 1/(5000 / 5951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5584 : Bounds (2176517 / 12500000) (174121361 / 1000000000) (Real.log (5951 / 5000)) := by
  have h := reflection_log_5584_neg
  have he : Real.log (5951 / 5000) = -Real.log (5000 / 5951) := by
    rw [show ((5951 / 5000) : ℝ) = ((5000 / 5951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5585_neg : (8438719 / 40000000) ≤ -Real.log (4049 / 5000) ∧
    -Real.log (4049 / 5000) ≤ (26370997 / 125000000) := by
  have h := checkLog_sound (w := (951 / 9049)) (n := 12)
    (lo := (8438719 / 40000000)) (hi := (26370997 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4049) = 1/(4049 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5585 : Bounds (-26370997 / 125000000) (-8438719 / 40000000) (Real.log (4049 / 5000)) := by
  have h := reflection_log_5585_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5586_neg : (190181 / 1000000000) ≤ -Real.log (5000000 / 5000951) ∧
    -Real.log (5000000 / 5000951) ≤ (95091 / 500000000) := by
  have h := checkLog_sound (w := (951 / 10000951)) (n := 12)
    (lo := (190181 / 1000000000)) (hi := (95091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000951 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000951 / 5000000) = 1/(5000000 / 5000951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5586 : Bounds (190181 / 1000000000) (95091 / 500000000) (Real.log (5000951 / 5000000)) := by
  have h := reflection_log_5586_neg
  have he : Real.log (5000951 / 5000000) = -Real.log (5000000 / 5000951) := by
    rw [show ((5000951 / 5000000) : ℝ) = ((5000000 / 5000951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5587_neg : (95109 / 500000000) ≤ -Real.log (4999049 / 5000000) ∧
    -Real.log (4999049 / 5000000) ≤ (190219 / 1000000000) := by
  have h := checkLog_sound (w := (951 / 9999049)) (n := 12)
    (lo := (95109 / 500000000)) (hi := (190219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999049) = 1/(4999049 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5587 : Bounds (-190219 / 1000000000) (-95109 / 500000000) (Real.log (4999049 / 5000000)) := by
  have h := reflection_log_5587_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5588_neg : (5705301 / 62500000) ≤ -Real.log (1000000 / 1095581) ∧
    -Real.log (1000000 / 1095581) ≤ (91284817 / 1000000000) := by
  have h := checkLog_sound (w := (95581 / 2095581)) (n := 12)
    (lo := (5705301 / 62500000)) (hi := (91284817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095581 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095581 / 1000000) = 1/(1000000 / 1095581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5588 : Bounds (5705301 / 62500000) (91284817 / 1000000000) (Real.log (1095581 / 1000000)) := by
  have h := reflection_log_5588_neg
  have he : Real.log (1095581 / 1000000) = -Real.log (1000000 / 1095581) := by
    rw [show ((1095581 / 1000000) : ℝ) = ((1000000 / 1095581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5589_neg : (10046253 / 100000000) ≤ -Real.log (904419 / 1000000) ∧
    -Real.log (904419 / 1000000) ≤ (100462531 / 1000000000) := by
  have h := checkLog_sound (w := (95581 / 1904419)) (n := 12)
    (lo := (10046253 / 100000000)) (hi := (100462531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904419) = 1/(904419 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5589 : Bounds (-100462531 / 1000000000) (-10046253 / 100000000) (Real.log (904419 / 1000000)) := by
  have h := reflection_log_5589_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5590_neg : (45752383 / 500000000) ≤ -Real.log (500000 / 547911) ∧
    -Real.log (500000 / 547911) ≤ (91504767 / 1000000000) := by
  have h := checkLog_sound (w := (47911 / 1047911)) (n := 12)
    (lo := (45752383 / 500000000)) (hi := (91504767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547911 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547911 / 500000) = 1/(500000 / 547911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5590 : Bounds (45752383 / 500000000) (91504767 / 1000000000) (Real.log (547911 / 500000)) := by
  have h := reflection_log_5590_neg
  have he : Real.log (547911 / 500000) = -Real.log (500000 / 547911) := by
    rw [show ((547911 / 500000) : ℝ) = ((500000 / 547911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5591_neg : (20145807 / 200000000) ≤ -Real.log (452089 / 500000) ∧
    -Real.log (452089 / 500000) ≤ (25182259 / 250000000) := by
  have h := checkLog_sound (w := (47911 / 952089)) (n := 12)
    (lo := (20145807 / 200000000)) (hi := (25182259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452089) = 1/(452089 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5591 : Bounds (-25182259 / 250000000) (-20145807 / 200000000) (Real.log (452089 / 500000)) := by
  have h := reflection_log_5591_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5592_neg : (2306067 / 250000000) ≤ -Real.log (247704536079 / 250000000000) ∧
    -Real.log (247704536079 / 250000000000) ≤ (9224269 / 1000000000) := by
  have h := checkLog_sound (w := (2295463921 / 497704536079)) (n := 12)
    (lo := (2306067 / 250000000)) (hi := (9224269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247704536079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247704536079) = 1/(247704536079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5592 : Bounds (-9224269 / 1000000000) (-2306067 / 250000000) (Real.log (247704536079 / 250000000000)) := by
  have h := reflection_log_5592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5593_neg : (4588857 / 500000000) ≤ -Real.log (990864272439 / 1000000000000) ∧
    -Real.log (990864272439 / 1000000000000) ≤ (1835543 / 200000000) := by
  have h := checkLog_sound (w := (9135727561 / 1990864272439)) (n := 12)
    (lo := (4588857 / 500000000)) (hi := (1835543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990864272439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990864272439) = 1/(990864272439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5593 : Bounds (-1835543 / 200000000) (-4588857 / 500000000) (Real.log (990864272439 / 1000000000000)) := by
  have h := reflection_log_5593_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5594_neg : (95873673 / 500000000) ≤ -Real.log (125000000000 / 151420552863) ∧
    -Real.log (125000000000 / 151420552863) ≤ (191747347 / 1000000000) := by
  have h := checkLog_sound (w := (26420552863 / 276420552863)) (n := 12)
    (lo := (95873673 / 500000000)) (hi := (191747347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151420552863 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151420552863 / 125000000000) = 1/(125000000000 / 151420552863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5594 : Bounds (95873673 / 500000000) (191747347 / 1000000000) (Real.log (151420552863 / 125000000000)) := by
  have h := reflection_log_5594_neg
  have he : Real.log (151420552863 / 125000000000) = -Real.log (125000000000 / 151420552863) := by
    rw [show ((151420552863 / 125000000000) : ℝ) = ((125000000000 / 151420552863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5595_neg : (192233801 / 1000000000) ≤ -Real.log (250000000000 / 302988460237) ∧
    -Real.log (250000000000 / 302988460237) ≤ (96116901 / 500000000) := by
  have h := checkLog_sound (w := (52988460237 / 552988460237)) (n := 12)
    (lo := (192233801 / 1000000000)) (hi := (96116901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302988460237 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302988460237 / 250000000000) = 1/(250000000000 / 302988460237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5595 : Bounds (192233801 / 1000000000) (96116901 / 500000000) (Real.log (302988460237 / 250000000000)) := by
  have h := reflection_log_5595_neg
  have he : Real.log (302988460237 / 250000000000) = -Real.log (250000000000 / 302988460237) := by
    rw [show ((302988460237 / 250000000000) : ℝ) = ((250000000000 / 302988460237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5596_neg : (48110229 / 125000000) ≤ -Real.log (500000000000 / 734720335843) ∧
    -Real.log (500000000000 / 734720335843) ≤ (384881833 / 1000000000) := by
  have h := checkLog_sound (w := (234720335843 / 1234720335843)) (n := 12)
    (lo := (48110229 / 125000000)) (hi := (384881833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734720335843 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734720335843 / 500000000000) = 1/(500000000000 / 734720335843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5596 : Bounds (48110229 / 125000000) (384881833 / 1000000000) (Real.log (734720335843 / 500000000000)) := by
  have h := reflection_log_5596_neg
  have he : Real.log (734720335843 / 500000000000) = -Real.log (500000000000 / 734720335843) := by
    rw [show ((734720335843 / 500000000000) : ℝ) = ((500000000000 / 734720335843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5597_neg : (77017867 / 200000000) ≤ -Real.log (500000000000 / 734872808101) ∧
    -Real.log (500000000000 / 734872808101) ≤ (48136167 / 125000000) := by
  have h := checkLog_sound (w := (234872808101 / 1234872808101)) (n := 12)
    (lo := (77017867 / 200000000)) (hi := (48136167 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734872808101 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734872808101 / 500000000000) = 1/(500000000000 / 734872808101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5597 : Bounds (77017867 / 200000000) (48136167 / 125000000) (Real.log (734872808101 / 500000000000)) := by
  have h := reflection_log_5597_neg
  have he : Real.log (734872808101 / 500000000000) = -Real.log (500000000000 / 734872808101) := by
    rw [show ((734872808101 / 500000000000) : ℝ) = ((500000000000 / 734872808101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5598_neg : (2721959 / 15625000) ≤ -Real.log (10000 / 11903) ∧
    -Real.log (10000 / 11903) ≤ (174205377 / 1000000000) := by
  have h := checkLog_sound (w := (1903 / 21903)) (n := 12)
    (lo := (2721959 / 15625000)) (hi := (174205377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11903 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11903 / 10000) = 1/(10000 / 11903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5598 : Bounds (2721959 / 15625000) (174205377 / 1000000000) (Real.log (11903 / 10000)) := by
  have h := reflection_log_5598_neg
  have he : Real.log (11903 / 10000) = -Real.log (10000 / 11903) := by
    rw [show ((11903 / 10000) : ℝ) = ((10000 / 11903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5599_neg : (21109147 / 100000000) ≤ -Real.log (8097 / 10000) ∧
    -Real.log (8097 / 10000) ≤ (211091471 / 1000000000) := by
  have h := checkLog_sound (w := (1903 / 18097)) (n := 12)
    (lo := (21109147 / 100000000)) (hi := (211091471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8097) = 1/(8097 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5599 : Bounds (-211091471 / 1000000000) (-21109147 / 100000000) (Real.log (8097 / 10000)) := by
  have h := reflection_log_5599_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5600_neg : (190281 / 1000000000) ≤ -Real.log (10000000 / 10001903) ∧
    -Real.log (10000000 / 10001903) ≤ (95141 / 500000000) := by
  have h := checkLog_sound (w := (1903 / 20001903)) (n := 12)
    (lo := (190281 / 1000000000)) (hi := (95141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001903 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001903 / 10000000) = 1/(10000000 / 10001903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5600 : Bounds (190281 / 1000000000) (95141 / 500000000) (Real.log (10001903 / 10000000)) := by
  have h := reflection_log_5600_neg
  have he : Real.log (10001903 / 10000000) = -Real.log (10000000 / 10001903) := by
    rw [show ((10001903 / 10000000) : ℝ) = ((10000000 / 10001903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5601_neg : (95159 / 500000000) ≤ -Real.log (9998097 / 10000000) ∧
    -Real.log (9998097 / 10000000) ≤ (190319 / 1000000000) := by
  have h := checkLog_sound (w := (1903 / 19998097)) (n := 12)
    (lo := (95159 / 500000000)) (hi := (190319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998097) = 1/(9998097 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5601 : Bounds (-190319 / 1000000000) (-95159 / 500000000) (Real.log (9998097 / 10000000)) := by
  have h := reflection_log_5601_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5602_neg : (18266273 / 200000000) ≤ -Real.log (62500 / 68477) ∧
    -Real.log (62500 / 68477) ≤ (45665683 / 500000000) := by
  have h := checkLog_sound (w := (5977 / 130977)) (n := 12)
    (lo := (18266273 / 200000000)) (hi := (45665683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68477 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68477 / 62500) = 1/(62500 / 68477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5602 : Bounds (18266273 / 200000000) (45665683 / 500000000) (Real.log (68477 / 62500)) := by
  have h := reflection_log_5602_neg
  have he : Real.log (68477 / 62500) = -Real.log (62500 / 68477) := by
    rw [show ((68477 / 62500) : ℝ) = ((62500 / 68477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5603_neg : (100518921 / 1000000000) ≤ -Real.log (56523 / 62500) ∧
    -Real.log (56523 / 62500) ≤ (50259461 / 500000000) := by
  have h := checkLog_sound (w := (5977 / 119023)) (n := 12)
    (lo := (100518921 / 1000000000)) (hi := (50259461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56523) = 1/(56523 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5603 : Bounds (-50259461 / 500000000) (-100518921 / 1000000000) (Real.log (56523 / 62500)) := by
  have h := reflection_log_5603_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5604_neg : (18310261 / 200000000) ≤ -Real.log (1000000 / 1095873) ∧
    -Real.log (1000000 / 1095873) ≤ (45775653 / 500000000) := by
  have h := checkLog_sound (w := (95873 / 2095873)) (n := 12)
    (lo := (18310261 / 200000000)) (hi := (45775653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095873 / 1000000) = 1/(1000000 / 1095873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5604 : Bounds (18310261 / 200000000) (45775653 / 500000000) (Real.log (1095873 / 1000000)) := by
  have h := reflection_log_5604_neg
  have he : Real.log (1095873 / 1000000) = -Real.log (1000000 / 1095873) := by
    rw [show ((1095873 / 1000000) : ℝ) = ((1000000 / 1095873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5605_neg : (100785441 / 1000000000) ≤ -Real.log (904127 / 1000000) ∧
    -Real.log (904127 / 1000000) ≤ (50392721 / 500000000) := by
  have h := checkLog_sound (w := (95873 / 1904127)) (n := 12)
    (lo := (100785441 / 1000000000)) (hi := (50392721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904127) = 1/(904127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5605 : Bounds (-50392721 / 500000000) (-100785441 / 1000000000) (Real.log (904127 / 1000000)) := by
  have h := reflection_log_5605_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5606_neg : (1846827 / 200000000) ≤ -Real.log (990808367871 / 1000000000000) ∧
    -Real.log (990808367871 / 1000000000000) ≤ (1154267 / 125000000) := by
  have h := checkLog_sound (w := (9191632129 / 1990808367871)) (n := 12)
    (lo := (1846827 / 200000000)) (hi := (1154267 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990808367871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990808367871) = 1/(990808367871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5606 : Bounds (-1154267 / 125000000) (-1846827 / 200000000) (Real.log (990808367871 / 1000000000000)) := by
  have h := reflection_log_5606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5607_neg : (2296889 / 250000000) ≤ -Real.log (3870525471 / 3906250000) ∧
    -Real.log (3870525471 / 3906250000) ≤ (9187557 / 1000000000) := by
  have h := checkLog_sound (w := (35724529 / 7776775471)) (n := 12)
    (lo := (2296889 / 250000000)) (hi := (9187557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3870525471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3870525471) = 1/(3870525471 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5607 : Bounds (-9187557 / 1000000000) (-2296889 / 250000000) (Real.log (3870525471 / 3906250000)) := by
  have h := reflection_log_5607_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5608_neg : (191850287 / 1000000000) ≤ -Real.log (500000000000 / 605744564159) ∧
    -Real.log (500000000000 / 605744564159) ≤ (11990643 / 62500000) := by
  have h := checkLog_sound (w := (105744564159 / 1105744564159)) (n := 12)
    (lo := (191850287 / 1000000000)) (hi := (11990643 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605744564159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605744564159 / 500000000000) = 1/(500000000000 / 605744564159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5608 : Bounds (191850287 / 1000000000) (11990643 / 62500000) (Real.log (605744564159 / 500000000000)) := by
  have h := reflection_log_5608_neg
  have he : Real.log (605744564159 / 500000000000) = -Real.log (500000000000 / 605744564159) := by
    rw [show ((605744564159 / 500000000000) : ℝ) = ((500000000000 / 605744564159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5609_neg : (192336747 / 1000000000) ≤ -Real.log (20000000000 / 24241572257) ∧
    -Real.log (20000000000 / 24241572257) ≤ (48084187 / 250000000) := by
  have h := checkLog_sound (w := (4241572257 / 44241572257)) (n := 12)
    (lo := (192336747 / 1000000000)) (hi := (48084187 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24241572257 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24241572257 / 20000000000) = 1/(20000000000 / 24241572257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5609 : Bounds (192336747 / 1000000000) (48084187 / 250000000) (Real.log (24241572257 / 20000000000)) := by
  have h := reflection_log_5609_neg
  have he : Real.log (24241572257 / 20000000000) = -Real.log (20000000000 / 24241572257) := by
    rw [show ((24241572257 / 20000000000) : ℝ) = ((20000000000 / 24241572257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5610_neg : (77017867 / 200000000) ≤ -Real.log (5000000000 / 7348728081) ∧
    -Real.log (5000000000 / 7348728081) ≤ (48136167 / 125000000) := by
  have h := checkLog_sound (w := (2348728081 / 12348728081)) (n := 12)
    (lo := (77017867 / 200000000)) (hi := (48136167 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7348728081 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7348728081 / 5000000000) = 1/(5000000000 / 7348728081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5610 : Bounds (77017867 / 200000000) (48136167 / 125000000) (Real.log (7348728081 / 5000000000)) := by
  have h := reflection_log_5610_neg
  have he : Real.log (7348728081 / 5000000000) = -Real.log (5000000000 / 7348728081) := by
    rw [show ((7348728081 / 5000000000) : ℝ) = ((5000000000 / 7348728081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5611_neg : (192648423 / 500000000) ≤ -Real.log (25000000000 / 36751265901) ∧
    -Real.log (25000000000 / 36751265901) ≤ (385296847 / 1000000000) := by
  have h := checkLog_sound (w := (11751265901 / 61751265901)) (n := 12)
    (lo := (192648423 / 500000000)) (hi := (385296847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36751265901 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36751265901 / 25000000000) = 1/(25000000000 / 36751265901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5611 : Bounds (192648423 / 500000000) (385296847 / 1000000000) (Real.log (36751265901 / 25000000000)) := by
  have h := reflection_log_5611_neg
  have he : Real.log (36751265901 / 25000000000) = -Real.log (25000000000 / 36751265901) := by
    rw [show ((36751265901 / 25000000000) : ℝ) = ((25000000000 / 36751265901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5612_neg : (34857877 / 200000000) ≤ -Real.log (625 / 744) ∧
    -Real.log (625 / 744) ≤ (87144693 / 500000000) := by
  have h := checkLog_sound (w := (119 / 1369)) (n := 12)
    (lo := (34857877 / 200000000)) (hi := (87144693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(744 / 625) = 1/(625 / 744) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5612 : Bounds (34857877 / 200000000) (87144693 / 500000000) (Real.log (744 / 625)) := by
  have h := reflection_log_5612_neg
  have he : Real.log (744 / 625) = -Real.log (625 / 744) := by
    rw [show ((744 / 625) : ℝ) = ((625 / 744) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5613_neg : (10560749 / 50000000) ≤ -Real.log (506 / 625) ∧
    -Real.log (506 / 625) ≤ (211214981 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 1131)) (n := 12)
    (lo := (10560749 / 50000000)) (hi := (211214981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 506) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 506) = 1/(506 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5613 : Bounds (-211214981 / 1000000000) (-10560749 / 50000000) (Real.log (506 / 625)) := by
  have h := reflection_log_5613_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5614_neg : (190381 / 1000000000) ≤ -Real.log (625000 / 625119) ∧
    -Real.log (625000 / 625119) ≤ (95191 / 500000000) := by
  have h := checkLog_sound (w := (119 / 1250119)) (n := 12)
    (lo := (190381 / 1000000000)) (hi := (95191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625119 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625119 / 625000) = 1/(625000 / 625119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5614 : Bounds (190381 / 1000000000) (95191 / 500000000) (Real.log (625119 / 625000)) := by
  have h := reflection_log_5614_neg
  have he : Real.log (625119 / 625000) = -Real.log (625000 / 625119) := by
    rw [show ((625119 / 625000) : ℝ) = ((625000 / 625119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5615_neg : (95209 / 500000000) ≤ -Real.log (624881 / 625000) ∧
    -Real.log (624881 / 625000) ≤ (190419 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 1249881)) (n := 12)
    (lo := (95209 / 500000000)) (hi := (190419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624881) = 1/(624881 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5615 : Bounds (-190419 / 1000000000) (-95209 / 500000000) (Real.log (624881 / 625000)) := by
  have h := reflection_log_5615_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5616_neg : (91377913 / 1000000000) ≤ -Real.log (1000000 / 1095683) ∧
    -Real.log (1000000 / 1095683) ≤ (45688957 / 500000000) := by
  have h := checkLog_sound (w := (95683 / 2095683)) (n := 12)
    (lo := (91377913 / 1000000000)) (hi := (45688957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095683 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1095683 / 1000000) = 1/(1000000 / 1095683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5616 : Bounds (91377913 / 1000000000) (45688957 / 500000000) (Real.log (1095683 / 1000000)) := by
  have h := reflection_log_5616_neg
  have he : Real.log (1095683 / 1000000) = -Real.log (1000000 / 1095683) := by
    rw [show ((1095683 / 1000000) : ℝ) = ((1000000 / 1095683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5617_neg : (25143829 / 250000000) ≤ -Real.log (904317 / 1000000) ∧
    -Real.log (904317 / 1000000) ≤ (100575317 / 1000000000) := by
  have h := checkLog_sound (w := (95683 / 1904317)) (n := 12)
    (lo := (25143829 / 250000000)) (hi := (100575317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 904317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 904317) = 1/(904317 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5617 : Bounds (-100575317 / 1000000000) (-25143829 / 250000000) (Real.log (904317 / 1000000)) := by
  have h := reflection_log_5617_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5618_neg : (91597843 / 1000000000) ≤ -Real.log (250000 / 273981) ∧
    -Real.log (250000 / 273981) ≤ (22899461 / 250000000) := by
  have h := checkLog_sound (w := (23981 / 523981)) (n := 12)
    (lo := (91597843 / 1000000000)) (hi := (22899461 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273981 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273981 / 250000) = 1/(250000 / 273981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5618 : Bounds (91597843 / 1000000000) (22899461 / 250000000) (Real.log (273981 / 250000)) := by
  have h := reflection_log_5618_neg
  have he : Real.log (273981 / 250000) = -Real.log (250000 / 273981) := by
    rw [show ((273981 / 250000) : ℝ) = ((250000 / 273981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5619_neg : (100841851 / 1000000000) ≤ -Real.log (226019 / 250000) ∧
    -Real.log (226019 / 250000) ≤ (25210463 / 250000000) := by
  have h := checkLog_sound (w := (23981 / 476019)) (n := 12)
    (lo := (100841851 / 1000000000)) (hi := (25210463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226019) = 1/(226019 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5619 : Bounds (-25210463 / 250000000) (-100841851 / 1000000000) (Real.log (226019 / 250000)) := by
  have h := reflection_log_5619_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5620_neg : (1155501 / 125000000) ≤ -Real.log (61924911639 / 62500000000) ∧
    -Real.log (61924911639 / 62500000000) ≤ (9244009 / 1000000000) := by
  have h := checkLog_sound (w := (575088361 / 124424911639)) (n := 12)
    (lo := (1155501 / 125000000)) (hi := (9244009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61924911639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61924911639) = 1/(61924911639 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5620 : Bounds (-9244009 / 1000000000) (-1155501 / 125000000) (Real.log (61924911639 / 62500000000)) := by
  have h := reflection_log_5620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5621_neg : (9197403 / 1000000000) ≤ -Real.log (990844763511 / 1000000000000) ∧
    -Real.log (990844763511 / 1000000000000) ≤ (2299351 / 250000000) := by
  have h := checkLog_sound (w := (9155236489 / 1990844763511)) (n := 12)
    (lo := (9197403 / 1000000000)) (hi := (2299351 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990844763511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990844763511) = 1/(990844763511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5621 : Bounds (-2299351 / 250000000) (-9197403 / 1000000000) (Real.log (990844763511 / 1000000000000)) := by
  have h := reflection_log_5621_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5622_neg : (191953229 / 1000000000) ≤ -Real.log (500000000000 / 605806923899) ∧
    -Real.log (500000000000 / 605806923899) ≤ (19195323 / 100000000) := by
  have h := checkLog_sound (w := (105806923899 / 1105806923899)) (n := 12)
    (lo := (191953229 / 1000000000)) (hi := (19195323 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605806923899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605806923899 / 500000000000) = 1/(500000000000 / 605806923899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5622 : Bounds (191953229 / 1000000000) (19195323 / 100000000) (Real.log (605806923899 / 500000000000)) := by
  have h := reflection_log_5622_neg
  have he : Real.log (605806923899 / 500000000000) = -Real.log (500000000000 / 605806923899) := by
    rw [show ((605806923899 / 500000000000) : ℝ) = ((500000000000 / 605806923899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5623_neg : (96219847 / 500000000) ≤ -Real.log (100000000000 / 121220339883) ∧
    -Real.log (100000000000 / 121220339883) ≤ (38487939 / 200000000) := by
  have h := checkLog_sound (w := (21220339883 / 221220339883)) (n := 12)
    (lo := (96219847 / 500000000)) (hi := (38487939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121220339883 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121220339883 / 100000000000) = 1/(100000000000 / 121220339883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5623 : Bounds (96219847 / 500000000) (38487939 / 200000000) (Real.log (121220339883 / 100000000000)) := by
  have h := reflection_log_5623_neg
  have he : Real.log (121220339883 / 100000000000) = -Real.log (100000000000 / 121220339883) := by
    rw [show ((121220339883 / 100000000000) : ℝ) = ((100000000000 / 121220339883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5624_neg : (192648423 / 500000000) ≤ -Real.log (500000000000 / 735025318019) ∧
    -Real.log (500000000000 / 735025318019) ≤ (385296847 / 1000000000) := by
  have h := checkLog_sound (w := (235025318019 / 1235025318019)) (n := 12)
    (lo := (192648423 / 500000000)) (hi := (385296847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735025318019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735025318019 / 500000000000) = 1/(500000000000 / 735025318019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5624 : Bounds (192648423 / 500000000) (385296847 / 1000000000) (Real.log (735025318019 / 500000000000)) := by
  have h := reflection_log_5624_neg
  have he : Real.log (735025318019 / 500000000000) = -Real.log (500000000000 / 735025318019) := by
    rw [show ((735025318019 / 500000000000) : ℝ) = ((500000000000 / 735025318019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5625_neg : (77100873 / 200000000) ≤ -Real.log (500000000000 / 735177865613) ∧
    -Real.log (500000000000 / 735177865613) ≤ (192752183 / 500000000) := by
  have h := checkLog_sound (w := (235177865613 / 1235177865613)) (n := 12)
    (lo := (77100873 / 200000000)) (hi := (192752183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735177865613 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735177865613 / 500000000000) = 1/(500000000000 / 735177865613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5625 : Bounds (77100873 / 200000000) (192752183 / 500000000) (Real.log (735177865613 / 500000000000)) := by
  have h := reflection_log_5625_neg
  have he : Real.log (735177865613 / 500000000000) = -Real.log (500000000000 / 735177865613) := by
    rw [show ((735177865613 / 500000000000) : ℝ) = ((500000000000 / 735177865613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5626_neg : (87186693 / 500000000) ≤ -Real.log (2000 / 2381) ∧
    -Real.log (2000 / 2381) ≤ (174373387 / 1000000000) := by
  have h := checkLog_sound (w := (381 / 4381)) (n := 12)
    (lo := (87186693 / 500000000)) (hi := (174373387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2381 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2381 / 2000) = 1/(2000 / 2381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5626 : Bounds (87186693 / 500000000) (174373387 / 1000000000) (Real.log (2381 / 2000)) := by
  have h := reflection_log_5626_neg
  have he : Real.log (2381 / 2000) = -Real.log (2000 / 2381) := by
    rw [show ((2381 / 2000) : ℝ) = ((2000 / 2381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5627_neg : (42267701 / 200000000) ≤ -Real.log (1619 / 2000) ∧
    -Real.log (1619 / 2000) ≤ (105669253 / 500000000) := by
  have h := checkLog_sound (w := (381 / 3619)) (n := 12)
    (lo := (42267701 / 200000000)) (hi := (105669253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1619) = 1/(1619 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5627 : Bounds (-105669253 / 500000000) (-42267701 / 200000000) (Real.log (1619 / 2000)) := by
  have h := reflection_log_5627_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5628_neg : (190481 / 1000000000) ≤ -Real.log (2000000 / 2000381) ∧
    -Real.log (2000000 / 2000381) ≤ (95241 / 500000000) := by
  have h := checkLog_sound (w := (381 / 4000381)) (n := 12)
    (lo := (190481 / 1000000000)) (hi := (95241 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000381 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000381 / 2000000) = 1/(2000000 / 2000381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5628 : Bounds (190481 / 1000000000) (95241 / 500000000) (Real.log (2000381 / 2000000)) := by
  have h := reflection_log_5628_neg
  have he : Real.log (2000381 / 2000000) = -Real.log (2000000 / 2000381) := by
    rw [show ((2000381 / 2000000) : ℝ) = ((2000000 / 2000381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5629_neg : (95259 / 500000000) ≤ -Real.log (1999619 / 2000000) ∧
    -Real.log (1999619 / 2000000) ≤ (190519 / 1000000000) := by
  have h := checkLog_sound (w := (381 / 3999619)) (n := 12)
    (lo := (95259 / 500000000)) (hi := (190519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999619) = 1/(1999619 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5629 : Bounds (-190519 / 1000000000) (-95259 / 500000000) (Real.log (1999619 / 2000000)) := by
  have h := reflection_log_5629_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5630_neg : (45712229 / 500000000) ≤ -Real.log (500000 / 547867) ∧
    -Real.log (500000 / 547867) ≤ (91424459 / 1000000000) := by
  have h := checkLog_sound (w := (47867 / 1047867)) (n := 12)
    (lo := (45712229 / 500000000)) (hi := (91424459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547867 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547867 / 500000) = 1/(500000 / 547867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5630 : Bounds (45712229 / 500000000) (91424459 / 1000000000) (Real.log (547867 / 500000)) := by
  have h := reflection_log_5630_neg
  have he : Real.log (547867 / 500000) = -Real.log (500000 / 547867) := by
    rw [show ((547867 / 500000) : ℝ) = ((500000 / 547867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5631_neg : (50315857 / 500000000) ≤ -Real.log (452133 / 500000) ∧
    -Real.log (452133 / 500000) ≤ (20126343 / 200000000) := by
  have h := checkLog_sound (w := (47867 / 952133)) (n := 12)
    (lo := (50315857 / 500000000)) (hi := (20126343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452133) = 1/(452133 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5631 : Bounds (-20126343 / 200000000) (-50315857 / 500000000) (Real.log (452133 / 500000)) := by
  have h := reflection_log_5631_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
