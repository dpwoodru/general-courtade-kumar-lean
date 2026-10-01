import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0080
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

theorem reflection_log_1_neg : (675194013 / 1000000000) ≤ -Real.log (25600 / 50289) ∧
    -Real.log (25600 / 50289) ≤ (337597007 / 500000000) := by
  have h := checkLog_sound (w := (24689 / 75889)) (n := 12)
    (lo := (675194013 / 1000000000)) (hi := (337597007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50289 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50289 / 25600) = 1/(25600 / 50289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (675194013 / 1000000000) (337597007 / 500000000) (Real.log (50289 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50289 / 25600) = -Real.log (25600 / 50289) := by
    rw [show ((50289 / 25600) : ℝ) = ((25600 / 50289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (333580473 / 100000000) ≤ -Real.log (911 / 25600) ∧
    -Real.log (911 / 25600) ≤ (667160947 / 200000000) := by
  have h := checkLog_sound (w := (689 / 2511)) (n := 12)
    (lo := (56321601 / 100000000)) (hi := (563216011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 911) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 911) = 1/(911 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-667160947 / 200000000) (-333580473 / 100000000) (Real.log (911 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (675005087 / 1000000000) ≤ -Real.log (51200 / 100559) ∧
    -Real.log (51200 / 100559) ≤ (21093909 / 31250000) := by
  have h := checkLog_sound (w := (49359 / 151759)) (n := 12)
    (lo := (675005087 / 1000000000)) (hi := (21093909 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100559 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100559 / 51200) = 1/(51200 / 100559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (675005087 / 1000000000) (21093909 / 31250000) (Real.log (100559 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100559 / 51200) = -Real.log (51200 / 100559) := by
    rw [show ((100559 / 51200) : ℝ) = ((51200 / 100559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3325430627 / 1000000000) ≤ -Real.log (1841 / 51200) ∧
    -Real.log (1841 / 51200) ≤ (415678829 / 125000000) := by
  have h := checkLog_sound (w := (1359 / 5041)) (n := 12)
    (lo := (552841907 / 1000000000)) (hi := (138210477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1841) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1841) = 1/(1841 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-415678829 / 125000000) (-3325430627 / 1000000000) (Real.log (1841 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (656912629 / 1000000000) ≤ -Real.log (12800 / 24689) ∧
    -Real.log (12800 / 24689) ≤ (65691263 / 100000000) := by
  have h := checkLog_sound (w := (11889 / 37489)) (n := 12)
    (lo := (656912629 / 1000000000)) (hi := (65691263 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24689 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24689 / 12800) = 1/(12800 / 24689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (656912629 / 1000000000) (65691263 / 100000000) (Real.log (24689 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24689 / 12800) = -Real.log (12800 / 24689) := by
    rw [show ((24689 / 12800) : ℝ) = ((12800 / 24689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (52853151 / 20000000) ≤ -Real.log (911 / 12800) ∧
    -Real.log (911 / 12800) ≤ (1321328777 / 500000000) := by
  have h := checkLog_sound (w := (689 / 2511)) (n := 12)
    (lo := (56321601 / 100000000)) (hi := (563216011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 911) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 911) = 1/(911 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1321328777 / 500000000) (-52853151 / 20000000) (Real.log (911 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (82065971 / 125000000) ≤ -Real.log (25600 / 49359) ∧
    -Real.log (25600 / 49359) ≤ (656527769 / 1000000000) := by
  have h := checkLog_sound (w := (23759 / 74959)) (n := 12)
    (lo := (82065971 / 125000000)) (hi := (656527769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49359 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49359 / 25600) = 1/(25600 / 49359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (82065971 / 125000000) (656527769 / 1000000000) (Real.log (49359 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49359 / 25600) = -Real.log (25600 / 49359) := by
    rw [show ((49359 / 25600) : ℝ) = ((25600 / 49359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2632283447 / 1000000000) ≤ -Real.log (1841 / 25600) ∧
    -Real.log (1841 / 25600) ≤ (2632283451 / 1000000000) := by
  have h := checkLog_sound (w := (1359 / 5041)) (n := 12)
    (lo := (552841907 / 1000000000)) (hi := (138210477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1841) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1841) = 1/(1841 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2632283451 / 1000000000) (-2632283447 / 1000000000) (Real.log (1841 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (678141151 / 1000000000) ≤ -Real.log (250000 / 492553) ∧
    -Real.log (250000 / 492553) ≤ (21191911 / 31250000) := by
  have h := checkLog_sound (w := (242553 / 742553)) (n := 12)
    (lo := (678141151 / 1000000000)) (hi := (21191911 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((492553 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(492553 / 250000) = 1/(250000 / 492553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (678141151 / 1000000000) (21191911 / 31250000) (Real.log (492553 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (492553 / 250000) = -Real.log (250000 / 492553) := by
    rw [show ((492553 / 250000) : ℝ) = ((250000 / 492553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (219603103 / 62500000) ≤ -Real.log (7447 / 250000) ∧
    -Real.log (7447 / 250000) ≤ (1756824827 / 500000000) := by
  have h := checkLog_sound (w := (731 / 30519)) (n := 12)
    (lo := (11978437 / 250000000)) (hi := (47913749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14894) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14894) = 1/(7447 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1756824827 / 500000000) (-219603103 / 62500000) (Real.log (7447 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (678289347 / 1000000000) ≤ -Real.log (125000 / 246313) ∧
    -Real.log (125000 / 246313) ≤ (169572337 / 250000000) := by
  have h := checkLog_sound (w := (121313 / 371313)) (n := 12)
    (lo := (678289347 / 1000000000)) (hi := (169572337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246313 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246313 / 125000) = 1/(125000 / 246313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (678289347 / 1000000000) (169572337 / 250000000) (Real.log (246313 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (246313 / 125000) = -Real.log (125000 / 246313) := by
    rw [show ((246313 / 125000) : ℝ) = ((125000 / 246313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (704700123 / 200000000) ≤ -Real.log (3687 / 125000) ∧
    -Real.log (3687 / 125000) ≤ (3523500621 / 1000000000) := by
  have h := checkLog_sound (w := (877 / 30373)) (n := 12)
    (lo := (11552943 / 200000000)) (hi := (14441179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14748) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14748) = 1/(3687 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3523500621 / 1000000000) (-704700123 / 200000000) (Real.log (3687 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (33901271 / 50000000) ≤ -Real.log (15625 / 30781) ∧
    -Real.log (15625 / 30781) ≤ (678025421 / 1000000000) := by
  have h := checkLog_sound (w := (7578 / 23203)) (n := 12)
    (lo := (33901271 / 50000000)) (hi := (678025421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30781 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30781 / 15625) = 1/(15625 / 30781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (33901271 / 50000000) (678025421 / 1000000000) (Real.log (30781 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (30781 / 15625) = -Real.log (15625 / 30781) := by
    rw [show ((30781 / 15625) : ℝ) = ((15625 / 30781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3506024703 / 1000000000) ≤ -Real.log (469 / 15625) ∧
    -Real.log (469 / 15625) ≤ (3506024709 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 30633)) (n := 12)
    (lo := (40288803 / 1000000000)) (hi := (10072201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15008) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 15008) = 1/(469 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3506024709 / 1000000000) (-3506024703 / 1000000000) (Real.log (469 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (678176679 / 1000000000) ≤ -Real.log (500000 / 985141) ∧
    -Real.log (500000 / 985141) ≤ (16954417 / 25000000) := by
  have h := checkLog_sound (w := (485141 / 1485141)) (n := 12)
    (lo := (678176679 / 1000000000)) (hi := (16954417 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((985141 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(985141 / 500000) = 1/(500000 / 985141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (678176679 / 1000000000) (16954417 / 25000000) (Real.log (985141 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (985141 / 500000) = -Real.log (500000 / 985141) := by
    rw [show ((985141 / 500000) : ℝ) = ((500000 / 985141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3516002353 / 1000000000) ≤ -Real.log (14859 / 500000) ∧
    -Real.log (14859 / 500000) ≤ (3516002359 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 15242)) (n := 12)
    (lo := (50266453 / 1000000000)) (hi := (25133227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14859) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14859) = 1/(14859 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3516002359 / 1000000000) (-3516002353 / 1000000000) (Real.log (14859 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2095895399 / 500000000) ≤ -Real.log (1562500000 / 103345516651) ∧
    -Real.log (1562500000 / 103345516651) ≤ (838358161 / 200000000) := by
  have h := checkLog_sound (w := (3345516651 / 203345516651)) (n := 12)
    (lo := (16453859 / 500000000)) (hi := (32907719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103345516651 / 100000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(103345516651 / 100000000000) = 1/(1562500000 / 103345516651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2095895399 / 500000000) (838358161 / 200000000) (Real.log (103345516651 / 1562500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (103345516651 / 1562500000) = -Real.log (1562500000 / 103345516651) := by
    rw [show ((103345516651 / 1562500000) : ℝ) = ((1562500000 / 103345516651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2100894981 / 500000000) ≤ -Real.log (500000000000 / 33402902088419) ∧
    -Real.log (500000000000 / 33402902088419) ≤ (4201789969 / 1000000000) := by
  have h := checkLog_sound (w := (1402902088419 / 65402902088419)) (n := 12)
    (lo := (21453441 / 500000000)) (hi := (42906883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33402902088419 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(33402902088419 / 32000000000000) = 1/(500000000000 / 33402902088419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2100894981 / 500000000) (4201789969 / 1000000000) (Real.log (33402902088419 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (33402902088419 / 500000000000) = -Real.log (500000000000 / 33402902088419) := by
    rw [show ((33402902088419 / 500000000000) : ℝ) = ((500000000000 / 33402902088419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4184050123 / 1000000000) ≤ -Real.log (250000000000 / 16407782515991) ∧
    -Real.log (250000000000 / 16407782515991) ≤ (418405013 / 100000000) := by
  have h := checkLog_sound (w := (407782515991 / 32407782515991)) (n := 12)
    (lo := (25167043 / 1000000000)) (hi := (6291761 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16407782515991 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(16407782515991 / 16000000000000) = 1/(250000000000 / 16407782515991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4184050123 / 1000000000) (418405013 / 100000000) (Real.log (16407782515991 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (16407782515991 / 250000000000) = -Real.log (250000000000 / 16407782515991) := by
    rw [show ((16407782515991 / 250000000000) : ℝ) = ((250000000000 / 16407782515991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (524272379 / 125000000) ≤ -Real.log (500000000000 / 33149639948853) ∧
    -Real.log (500000000000 / 33149639948853) ≤ (4194179039 / 1000000000) := by
  have h := checkLog_sound (w := (1149639948853 / 65149639948853)) (n := 12)
    (lo := (2205997 / 62500000)) (hi := (35295953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33149639948853 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(33149639948853 / 32000000000000) = 1/(500000000000 / 33149639948853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (524272379 / 125000000) (4194179039 / 1000000000) (Real.log (33149639948853 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (33149639948853 / 500000000000) = -Real.log (500000000000 / 33149639948853) := by
    rw [show ((33149639948853 / 500000000000) : ℝ) = ((500000000000 / 33149639948853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0080
