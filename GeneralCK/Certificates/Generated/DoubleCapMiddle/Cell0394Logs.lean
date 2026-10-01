import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0394
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

theorem reflection_log_1_neg : (201664519 / 1000000000) ≤ -Real.log (640 / 783) ∧
    -Real.log (640 / 783) ≤ (5041613 / 25000000) := by
  have h := checkLog_sound (w := (143 / 1423)) (n := 12)
    (lo := (201664519 / 1000000000)) (hi := (5041613 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((783 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(783 / 640) = 1/(640 / 783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (201664519 / 1000000000) (5041613 / 25000000) (Real.log (783 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (783 / 640) = -Real.log (640 / 783) := by
    rw [show ((783 / 640) : ℝ) = ((640 / 783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (5057563 / 20000000) ≤ -Real.log (497 / 640) ∧
    -Real.log (497 / 640) ≤ (252878151 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 1137)) (n := 12)
    (lo := (5057563 / 20000000)) (hi := (252878151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 497) = 1/(497 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-252878151 / 1000000000) (-5057563 / 20000000) (Real.log (497 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (201425027 / 1000000000) ≤ -Real.log (2048 / 2505) ∧
    -Real.log (2048 / 2505) ≤ (50356257 / 250000000) := by
  have h := checkLog_sound (w := (457 / 4553)) (n := 12)
    (lo := (201425027 / 1000000000)) (hi := (50356257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2505 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2505 / 2048) = 1/(2048 / 2505) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (201425027 / 1000000000) (50356257 / 250000000) (Real.log (2505 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2505 / 2048) = -Real.log (2048 / 2505) := by
    rw [show ((2505 / 2048) : ℝ) = ((2048 / 2505) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (252500957 / 1000000000) ≤ -Real.log (1591 / 2048) ∧
    -Real.log (1591 / 2048) ≤ (126250479 / 500000000) := by
  have h := checkLog_sound (w := (457 / 3639)) (n := 12)
    (lo := (252500957 / 1000000000)) (hi := (126250479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1591) = 1/(1591 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-126250479 / 500000000) (-252500957 / 1000000000) (Real.log (1591 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (184703029 / 500000000) ≤ -Real.log (320 / 463) ∧
    -Real.log (320 / 463) ≤ (369406059 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 783)) (n := 12)
    (lo := (184703029 / 500000000)) (hi := (369406059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463 / 320) = 1/(320 / 463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (184703029 / 500000000) (369406059 / 1000000000) (Real.log (463 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (463 / 320) = -Real.log (320 / 463) := by
    rw [show ((463 / 320) : ℝ) = ((320 / 463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (592171263 / 1000000000) ≤ -Real.log (177 / 320) ∧
    -Real.log (177 / 320) ≤ (2313169 / 3906250) := by
  have h := checkLog_sound (w := (143 / 497)) (n := 12)
    (lo := (592171263 / 1000000000)) (hi := (2313169 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 177) = 1/(177 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2313169 / 3906250) (-592171263 / 1000000000) (Real.log (177 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23062563 / 62500000) ≤ -Real.log (1024 / 1481) ∧
    -Real.log (1024 / 1481) ≤ (369001009 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 2505)) (n := 12)
    (lo := (23062563 / 62500000)) (hi := (369001009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1481 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1481 / 1024) = 1/(1024 / 1481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23062563 / 62500000) (369001009 / 1000000000) (Real.log (1481 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1481 / 1024) = -Real.log (1024 / 1481) := by
    rw [show ((1481 / 1024) : ℝ) = ((1024 / 1481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (591112501 / 1000000000) ≤ -Real.log (567 / 1024) ∧
    -Real.log (567 / 1024) ≤ (295556251 / 500000000) := by
  have h := checkLog_sound (w := (457 / 1591)) (n := 12)
    (lo := (591112501 / 1000000000)) (hi := (295556251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 567) = 1/(567 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-295556251 / 500000000) (-591112501 / 1000000000) (Real.log (567 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (276445427 / 1000000000) ≤ -Real.log (200000 / 263687) ∧
    -Real.log (200000 / 263687) ≤ (69111357 / 250000000) := by
  have h := checkLog_sound (w := (63687 / 463687)) (n := 12)
    (lo := (276445427 / 1000000000)) (hi := (69111357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263687 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(263687 / 200000) = 1/(200000 / 263687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (276445427 / 1000000000) (69111357 / 250000000) (Real.log (263687 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (263687 / 200000) = -Real.log (200000 / 263687) := by
    rw [show ((263687 / 200000) : ℝ) = ((200000 / 263687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (191681827 / 500000000) ≤ -Real.log (136313 / 200000) ∧
    -Real.log (136313 / 200000) ≤ (76672731 / 200000000) := by
  have h := checkLog_sound (w := (63687 / 336313)) (n := 12)
    (lo := (191681827 / 500000000)) (hi := (76672731 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 136313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 136313) = 1/(136313 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-76672731 / 200000000) (-191681827 / 500000000) (Real.log (136313 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (276769243 / 1000000000) ≤ -Real.log (500000 / 659431) ∧
    -Real.log (500000 / 659431) ≤ (69192311 / 250000000) := by
  have h := checkLog_sound (w := (159431 / 1159431)) (n := 12)
    (lo := (276769243 / 1000000000)) (hi := (69192311 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659431 / 500000) = 1/(500000 / 659431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (276769243 / 1000000000) (69192311 / 250000000) (Real.log (659431 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (659431 / 500000) = -Real.log (500000 / 659431) := by
    rw [show ((659431 / 500000) : ℝ) = ((500000 / 659431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (7679807 / 20000000) ≤ -Real.log (340569 / 500000) ∧
    -Real.log (340569 / 500000) ≤ (383990351 / 1000000000) := by
  have h := checkLog_sound (w := (159431 / 840569)) (n := 12)
    (lo := (7679807 / 20000000)) (hi := (383990351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 340569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 340569) = 1/(340569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-383990351 / 1000000000) (-7679807 / 20000000) (Real.log (340569 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (52092743 / 250000000) ≤ -Real.log (100000 / 123167) ∧
    -Real.log (100000 / 123167) ≤ (208370973 / 1000000000) := by
  have h := checkLog_sound (w := (23167 / 223167)) (n := 12)
    (lo := (52092743 / 250000000)) (hi := (208370973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123167 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123167 / 100000) = 1/(100000 / 123167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (52092743 / 250000000) (208370973 / 1000000000) (Real.log (123167 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (123167 / 100000) = -Real.log (100000 / 123167) := by
    rw [show ((123167 / 100000) : ℝ) = ((100000 / 123167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (5270719 / 20000000) ≤ -Real.log (76833 / 100000) ∧
    -Real.log (76833 / 100000) ≤ (263535951 / 1000000000) := by
  have h := checkLog_sound (w := (23167 / 176833)) (n := 12)
    (lo := (5270719 / 20000000)) (hi := (263535951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 76833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 76833) = 1/(76833 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-263535951 / 1000000000) (-5270719 / 20000000) (Real.log (76833 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (208638053 / 1000000000) ≤ -Real.log (1000000 / 1231999) ∧
    -Real.log (1000000 / 1231999) ≤ (104319027 / 500000000) := by
  have h := checkLog_sound (w := (231999 / 2231999)) (n := 12)
    (lo := (208638053 / 1000000000)) (hi := (104319027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231999 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231999 / 1000000) = 1/(1000000 / 1231999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (208638053 / 1000000000) (104319027 / 500000000) (Real.log (1231999 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1231999 / 1000000) = -Real.log (1000000 / 1231999) := by
    rw [show ((1231999 / 1000000) : ℝ) = ((1000000 / 1231999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (263964243 / 1000000000) ≤ -Real.log (768001 / 1000000) ∧
    -Real.log (768001 / 1000000) ≤ (65991061 / 250000000) := by
  have h := checkLog_sound (w := (231999 / 1768001)) (n := 12)
    (lo := (263964243 / 1000000000)) (hi := (65991061 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 768001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 768001) = 1/(768001 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-65991061 / 250000000) (-263964243 / 1000000000) (Real.log (768001 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (659809081 / 1000000000) ≤ -Real.log (156250000 / 302253591) ∧
    -Real.log (156250000 / 302253591) ≤ (329904541 / 500000000) := by
  have h := checkLog_sound (w := (146003591 / 458503591)) (n := 12)
    (lo := (659809081 / 1000000000)) (hi := (329904541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302253591 / 156250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302253591 / 156250000) = 1/(156250000 / 302253591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (659809081 / 1000000000) (329904541 / 500000000) (Real.log (302253591 / 156250000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (302253591 / 156250000) = -Real.log (156250000 / 302253591) := by
    rw [show ((302253591 / 156250000) : ℝ) = ((156250000 / 302253591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (660759593 / 1000000000) ≤ -Real.log (500000000000 / 968131274427) ∧
    -Real.log (500000000000 / 968131274427) ≤ (330379797 / 500000000) := by
  have h := checkLog_sound (w := (468131274427 / 1468131274427)) (n := 12)
    (lo := (660759593 / 1000000000)) (hi := (330379797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((968131274427 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(968131274427 / 500000000000) = 1/(500000000000 / 968131274427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (660759593 / 1000000000) (330379797 / 500000000) (Real.log (968131274427 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (968131274427 / 500000000000) = -Real.log (500000000000 / 968131274427) := by
    rw [show ((968131274427 / 500000000000) : ℝ) = ((500000000000 / 968131274427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (235953461 / 500000000) ≤ -Real.log (500000000000 / 801524084703) ∧
    -Real.log (500000000000 / 801524084703) ≤ (471906923 / 1000000000) := by
  have h := checkLog_sound (w := (301524084703 / 1301524084703)) (n := 12)
    (lo := (235953461 / 500000000)) (hi := (471906923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801524084703 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(801524084703 / 500000000000) = 1/(500000000000 / 801524084703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (235953461 / 500000000) (471906923 / 1000000000) (Real.log (801524084703 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (801524084703 / 500000000000) = -Real.log (500000000000 / 801524084703) := by
    rw [show ((801524084703 / 500000000000) : ℝ) = ((500000000000 / 801524084703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (472602297 / 1000000000) ≤ -Real.log (100000000000 / 160416327583) ∧
    -Real.log (100000000000 / 160416327583) ≤ (236301149 / 500000000) := by
  have h := checkLog_sound (w := (60416327583 / 260416327583)) (n := 12)
    (lo := (472602297 / 1000000000)) (hi := (236301149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160416327583 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160416327583 / 100000000000) = 1/(100000000000 / 160416327583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (472602297 / 1000000000) (236301149 / 500000000) (Real.log (160416327583 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (160416327583 / 100000000000) = -Real.log (100000000000 / 160416327583) := by
    rw [show ((160416327583 / 100000000000) : ℝ) = ((100000000000 / 160416327583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0394
