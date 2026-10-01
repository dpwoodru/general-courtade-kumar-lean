import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0297
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

theorem reflection_log_1_neg : (8985073 / 40000000) ≤ -Real.log (10240 / 12819) ∧
    -Real.log (10240 / 12819) ≤ (112313413 / 500000000) := by
  have h := checkLog_sound (w := (2579 / 23059)) (n := 12)
    (lo := (8985073 / 40000000)) (hi := (112313413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12819 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12819 / 10240) = 1/(10240 / 12819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8985073 / 40000000) (112313413 / 500000000) (Real.log (12819 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12819 / 10240) = -Real.log (10240 / 12819) := by
    rw [show ((12819 / 10240) : ℝ) = ((10240 / 12819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (36269887 / 125000000) ≤ -Real.log (7661 / 10240) ∧
    -Real.log (7661 / 10240) ≤ (290159097 / 1000000000) := by
  have h := checkLog_sound (w := (2579 / 17901)) (n := 12)
    (lo := (36269887 / 125000000)) (hi := (290159097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7661) = 1/(7661 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-290159097 / 1000000000) (-36269887 / 125000000) (Real.log (7661 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (22439277 / 100000000) ≤ -Real.log (640 / 801) ∧
    -Real.log (640 / 801) ≤ (224392771 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1441)) (n := 12)
    (lo := (22439277 / 100000000)) (hi := (224392771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(801 / 640) = 1/(640 / 801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (22439277 / 100000000) (224392771 / 1000000000) (Real.log (801 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (801 / 640) = -Real.log (640 / 801) := by
    rw [show ((801 / 640) : ℝ) = ((640 / 801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (144883789 / 500000000) ≤ -Real.log (479 / 640) ∧
    -Real.log (479 / 640) ≤ (289767579 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1119)) (n := 12)
    (lo := (144883789 / 500000000)) (hi := (289767579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 479) = 1/(479 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-289767579 / 1000000000) (-144883789 / 500000000) (Real.log (479 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (407936011 / 1000000000) ≤ -Real.log (5120 / 7699) ∧
    -Real.log (5120 / 7699) ≤ (101984003 / 250000000) := by
  have h := checkLog_sound (w := (2579 / 12819)) (n := 12)
    (lo := (407936011 / 1000000000)) (hi := (101984003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7699 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7699 / 5120) = 1/(5120 / 7699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (407936011 / 1000000000) (101984003 / 250000000) (Real.log (7699 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7699 / 5120) = -Real.log (5120 / 7699) := by
    rw [show ((7699 / 5120) : ℝ) = ((5120 / 7699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (350298367 / 500000000) ≤ -Real.log (2541 / 5120) ∧
    -Real.log (2541 / 5120) ≤ (1368353 / 1953125) := by
  have h := checkLog_sound (w := (19 / 5101)) (n := 12)
    (lo := (3724777 / 500000000)) (hi := (1489911 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2541) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2541) = 1/(2541 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1368353 / 1953125) (-350298367 / 500000000) (Real.log (2541 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (203773137 / 500000000) ≤ -Real.log (320 / 481) ∧
    -Real.log (320 / 481) ≤ (16301851 / 40000000) := by
  have h := checkLog_sound (w := (161 / 801)) (n := 12)
    (lo := (203773137 / 500000000)) (hi := (16301851 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481 / 320) = 1/(320 / 481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (203773137 / 500000000) (16301851 / 40000000) (Real.log (481 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (481 / 320) = -Real.log (320 / 481) := by
    rw [show ((481 / 320) : ℝ) = ((320 / 481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (699416793 / 1000000000) ≤ -Real.log (159 / 320) ∧
    -Real.log (159 / 320) ≤ (139883359 / 200000000) := by
  have h := checkLog_sound (w := (1 / 319)) (n := 12)
    (lo := (6269613 / 1000000000)) (hi := (3134807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 159) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 159) = 1/(159 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-139883359 / 200000000) (-699416793 / 1000000000) (Real.log (159 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (153732423 / 500000000) ≤ -Real.log (1000000 / 1359973) ∧
    -Real.log (1000000 / 1359973) ≤ (307464847 / 1000000000) := by
  have h := checkLog_sound (w := (359973 / 2359973)) (n := 12)
    (lo := (153732423 / 500000000)) (hi := (307464847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359973 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359973 / 1000000) = 1/(1000000 / 1359973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (153732423 / 500000000) (307464847 / 1000000000) (Real.log (1359973 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1359973 / 1000000) = -Real.log (1000000 / 1359973) := by
    rw [show ((1359973 / 1000000) : ℝ) = ((1000000 / 1359973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (111561229 / 250000000) ≤ -Real.log (640027 / 1000000) ∧
    -Real.log (640027 / 1000000) ≤ (446244917 / 1000000000) := by
  have h := checkLog_sound (w := (359973 / 1640027)) (n := 12)
    (lo := (111561229 / 250000000)) (hi := (446244917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 640027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 640027) = 1/(640027 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-446244917 / 1000000000) (-111561229 / 250000000) (Real.log (640027 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (153890857 / 500000000) ≤ -Real.log (250000 / 340101) ∧
    -Real.log (250000 / 340101) ≤ (61556343 / 200000000) := by
  have h := checkLog_sound (w := (90101 / 590101)) (n := 12)
    (lo := (153890857 / 500000000)) (hi := (61556343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340101 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340101 / 250000) = 1/(250000 / 340101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (153890857 / 500000000) (61556343 / 200000000) (Real.log (340101 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (340101 / 250000) = -Real.log (250000 / 340101) := by
    rw [show ((340101 / 250000) : ℝ) = ((250000 / 340101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (446918551 / 1000000000) ≤ -Real.log (159899 / 250000) ∧
    -Real.log (159899 / 250000) ≤ (55864819 / 125000000) := by
  have h := checkLog_sound (w := (90101 / 409899)) (n := 12)
    (lo := (446918551 / 1000000000)) (hi := (55864819 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 159899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 159899) = 1/(159899 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-55864819 / 125000000) (-446918551 / 1000000000) (Real.log (159899 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (234283669 / 1000000000) ≤ -Real.log (1000000 / 1264003) ∧
    -Real.log (1000000 / 1264003) ≤ (23428367 / 100000000) := by
  have h := checkLog_sound (w := (264003 / 2264003)) (n := 12)
    (lo := (234283669 / 1000000000)) (hi := (23428367 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1264003 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1264003 / 1000000) = 1/(1000000 / 1264003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (234283669 / 1000000000) (23428367 / 100000000) (Real.log (1264003 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1264003 / 1000000) = -Real.log (1000000 / 1264003) := by
    rw [show ((1264003 / 1000000) : ℝ) = ((1000000 / 1264003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (76632309 / 250000000) ≤ -Real.log (735997 / 1000000) ∧
    -Real.log (735997 / 1000000) ≤ (306529237 / 1000000000) := by
  have h := checkLog_sound (w := (264003 / 1735997)) (n := 12)
    (lo := (76632309 / 250000000)) (hi := (306529237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 735997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 735997) = 1/(735997 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-306529237 / 1000000000) (-76632309 / 250000000) (Real.log (735997 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (234552619 / 1000000000) ≤ -Real.log (1000000 / 1264343) ∧
    -Real.log (1000000 / 1264343) ≤ (11727631 / 50000000) := by
  have h := checkLog_sound (w := (264343 / 2264343)) (n := 12)
    (lo := (234552619 / 1000000000)) (hi := (11727631 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1264343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1264343 / 1000000) = 1/(1000000 / 1264343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (234552619 / 1000000000) (11727631 / 50000000) (Real.log (1264343 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1264343 / 1000000) = -Real.log (1000000 / 1264343) := by
    rw [show ((1264343 / 1000000) : ℝ) = ((1000000 / 1264343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (306991301 / 1000000000) ≤ -Real.log (735657 / 1000000) ∧
    -Real.log (735657 / 1000000) ≤ (153495651 / 500000000) := by
  have h := checkLog_sound (w := (264343 / 1735657)) (n := 12)
    (lo := (306991301 / 1000000000)) (hi := (153495651 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 735657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 735657) = 1/(735657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-153495651 / 500000000) (-306991301 / 1000000000) (Real.log (735657 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (376854881 / 500000000) ≤ -Real.log (125000000000 / 265608521203) ∧
    -Real.log (125000000000 / 265608521203) ≤ (188427441 / 250000000) := by
  have h := checkLog_sound (w := (15608521203 / 515608521203)) (n := 12)
    (lo := (30281291 / 500000000)) (hi := (60562583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((265608521203 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(265608521203 / 250000000000) = 1/(125000000000 / 265608521203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (376854881 / 500000000) (188427441 / 250000000) (Real.log (265608521203 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (265608521203 / 125000000000) = -Real.log (125000000000 / 265608521203) := by
    rw [show ((265608521203 / 125000000000) : ℝ) = ((125000000000 / 265608521203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (150940053 / 200000000) ≤ -Real.log (250000000000 / 531743475569) ∧
    -Real.log (250000000000 / 531743475569) ≤ (754700267 / 1000000000) := by
  have h := checkLog_sound (w := (31743475569 / 1031743475569)) (n := 12)
    (lo := (12310617 / 200000000)) (hi := (30776543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((531743475569 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(531743475569 / 500000000000) = 1/(250000000000 / 531743475569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (150940053 / 200000000) (754700267 / 1000000000) (Real.log (531743475569 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (531743475569 / 250000000000) = -Real.log (250000000000 / 531743475569) := by
    rw [show ((531743475569 / 250000000000) : ℝ) = ((250000000000 / 531743475569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (108162581 / 200000000) ≤ -Real.log (250000000000 / 429350595179) ∧
    -Real.log (250000000000 / 429350595179) ≤ (270406453 / 500000000) := by
  have h := checkLog_sound (w := (179350595179 / 679350595179)) (n := 12)
    (lo := (108162581 / 200000000)) (hi := (270406453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429350595179 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(429350595179 / 250000000000) = 1/(250000000000 / 429350595179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (108162581 / 200000000) (270406453 / 500000000) (Real.log (429350595179 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (429350595179 / 250000000000) = -Real.log (250000000000 / 429350595179) := by
    rw [show ((429350595179 / 250000000000) : ℝ) = ((250000000000 / 429350595179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (541543921 / 1000000000) ≤ -Real.log (500000000000 / 859329143881) ∧
    -Real.log (500000000000 / 859329143881) ≤ (270771961 / 500000000) := by
  have h := checkLog_sound (w := (359329143881 / 1359329143881)) (n := 12)
    (lo := (541543921 / 1000000000)) (hi := (270771961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859329143881 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(859329143881 / 500000000000) = 1/(500000000000 / 859329143881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (541543921 / 1000000000) (270771961 / 500000000) (Real.log (859329143881 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (859329143881 / 500000000000) = -Real.log (500000000000 / 859329143881) := by
    rw [show ((859329143881 / 500000000000) : ℝ) = ((500000000000 / 859329143881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0297
