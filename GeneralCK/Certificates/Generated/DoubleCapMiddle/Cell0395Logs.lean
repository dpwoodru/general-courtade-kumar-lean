import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0395
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

theorem reflection_log_1_neg : (201425027 / 1000000000) ≤ -Real.log (2048 / 2505) ∧
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


theorem reflection_log_1 : Bounds (201425027 / 1000000000) (50356257 / 250000000) (Real.log (2505 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2505 / 2048) = -Real.log (2048 / 2505) := by
    rw [show ((2505 / 2048) : ℝ) = ((2048 / 2505) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (252500957 / 1000000000) ≤ -Real.log (1591 / 2048) ∧
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


theorem reflection_log_2 : Bounds (-126250479 / 500000000) (-252500957 / 1000000000) (Real.log (1591 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (201185477 / 1000000000) ≤ -Real.log (5120 / 6261) ∧
    -Real.log (5120 / 6261) ≤ (100592739 / 500000000) := by
  have h := checkLog_sound (w := (1141 / 11381)) (n := 12)
    (lo := (201185477 / 1000000000)) (hi := (100592739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6261 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6261 / 5120) = 1/(5120 / 6261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (201185477 / 1000000000) (100592739 / 500000000) (Real.log (6261 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6261 / 5120) = -Real.log (5120 / 6261) := by
    rw [show ((6261 / 5120) : ℝ) = ((5120 / 6261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (252123907 / 1000000000) ≤ -Real.log (3979 / 5120) ∧
    -Real.log (3979 / 5120) ≤ (63030977 / 250000000) := by
  have h := checkLog_sound (w := (1141 / 9099)) (n := 12)
    (lo := (252123907 / 1000000000)) (hi := (63030977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3979) = 1/(3979 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-63030977 / 250000000) (-252123907 / 1000000000) (Real.log (3979 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23062563 / 62500000) ≤ -Real.log (1024 / 1481) ∧
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


theorem reflection_log_5 : Bounds (23062563 / 62500000) (369001009 / 1000000000) (Real.log (1481 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1481 / 1024) = -Real.log (1024 / 1481) := by
    rw [show ((1481 / 1024) : ℝ) = ((1024 / 1481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (591112501 / 1000000000) ≤ -Real.log (567 / 1024) ∧
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


theorem reflection_log_6 : Bounds (-295556251 / 500000000) (-591112501 / 1000000000) (Real.log (567 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (184297897 / 500000000) ≤ -Real.log (2560 / 3701) ∧
    -Real.log (2560 / 3701) ≤ (73719159 / 200000000) := by
  have h := checkLog_sound (w := (1141 / 6261)) (n := 12)
    (lo := (184297897 / 500000000)) (hi := (73719159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3701 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3701 / 2560) = 1/(2560 / 3701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (184297897 / 500000000) (73719159 / 200000000) (Real.log (3701 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3701 / 2560) = -Real.log (2560 / 3701) := by
    rw [show ((3701 / 2560) : ℝ) = ((2560 / 3701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (29502743 / 50000000) ≤ -Real.log (1419 / 2560) ∧
    -Real.log (1419 / 2560) ≤ (590054861 / 1000000000) := by
  have h := checkLog_sound (w := (1141 / 3979)) (n := 12)
    (lo := (29502743 / 50000000)) (hi := (590054861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1419) = 1/(1419 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-590054861 / 1000000000) (-29502743 / 50000000) (Real.log (1419 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (34515283 / 125000000) ≤ -Real.log (1000000 / 1318009) ∧
    -Real.log (1000000 / 1318009) ≤ (55224453 / 200000000) := by
  have h := checkLog_sound (w := (318009 / 2318009)) (n := 12)
    (lo := (34515283 / 125000000)) (hi := (55224453 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1318009 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1318009 / 1000000) = 1/(1000000 / 1318009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (34515283 / 125000000) (55224453 / 200000000) (Real.log (1318009 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1318009 / 1000000) = -Real.log (1000000 / 1318009) := by
    rw [show ((1318009 / 1000000) : ℝ) = ((1000000 / 1318009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (382738817 / 1000000000) ≤ -Real.log (681991 / 1000000) ∧
    -Real.log (681991 / 1000000) ≤ (191369409 / 500000000) := by
  have h := checkLog_sound (w := (318009 / 1681991)) (n := 12)
    (lo := (382738817 / 1000000000)) (hi := (191369409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 681991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 681991) = 1/(681991 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-191369409 / 500000000) (-382738817 / 1000000000) (Real.log (681991 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (55289237 / 200000000) ≤ -Real.log (250000 / 329609) ∧
    -Real.log (250000 / 329609) ≤ (138223093 / 500000000) := by
  have h := checkLog_sound (w := (79609 / 579609)) (n := 12)
    (lo := (55289237 / 200000000)) (hi := (138223093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329609 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329609 / 250000) = 1/(250000 / 329609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (55289237 / 200000000) (138223093 / 500000000) (Real.log (329609 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (329609 / 250000) = -Real.log (250000 / 329609) := by
    rw [show ((329609 / 250000) : ℝ) = ((250000 / 329609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (383365121 / 1000000000) ≤ -Real.log (170391 / 250000) ∧
    -Real.log (170391 / 250000) ≤ (191682561 / 500000000) := by
  have h := checkLog_sound (w := (79609 / 420391)) (n := 12)
    (lo := (383365121 / 1000000000)) (hi := (191682561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 170391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 170391) = 1/(170391 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-191682561 / 500000000) (-383365121 / 1000000000) (Real.log (170391 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (208104631 / 1000000000) ≤ -Real.log (500000 / 615671) ∧
    -Real.log (500000 / 615671) ≤ (26013079 / 125000000) := by
  have h := checkLog_sound (w := (115671 / 1115671)) (n := 12)
    (lo := (208104631 / 1000000000)) (hi := (26013079 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615671 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615671 / 500000) = 1/(500000 / 615671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (208104631 / 1000000000) (26013079 / 125000000) (Real.log (615671 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (615671 / 500000) = -Real.log (500000 / 615671) := by
    rw [show ((615671 / 500000) : ℝ) = ((500000 / 615671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (263109141 / 1000000000) ≤ -Real.log (384329 / 500000) ∧
    -Real.log (384329 / 500000) ≤ (131554571 / 500000000) := by
  have h := checkLog_sound (w := (115671 / 884329)) (n := 12)
    (lo := (263109141 / 1000000000)) (hi := (131554571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 384329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 384329) = 1/(384329 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-131554571 / 500000000) (-263109141 / 1000000000) (Real.log (384329 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (208371783 / 1000000000) ≤ -Real.log (1000000 / 1231671) ∧
    -Real.log (1000000 / 1231671) ≤ (26046473 / 125000000) := by
  have h := checkLog_sound (w := (231671 / 2231671)) (n := 12)
    (lo := (208371783 / 1000000000)) (hi := (26046473 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231671 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231671 / 1000000) = 1/(1000000 / 1231671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (208371783 / 1000000000) (26046473 / 125000000) (Real.log (1231671 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1231671 / 1000000) = -Real.log (1000000 / 1231671) := by
    rw [show ((1231671 / 1000000) : ℝ) = ((1000000 / 1231671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (65884313 / 250000000) ≤ -Real.log (768329 / 1000000) ∧
    -Real.log (768329 / 1000000) ≤ (263537253 / 1000000000) := by
  have h := checkLog_sound (w := (231671 / 1768329)) (n := 12)
    (lo := (65884313 / 250000000)) (hi := (263537253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 768329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 768329) = 1/(768329 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-263537253 / 1000000000) (-65884313 / 250000000) (Real.log (768329 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (329430541 / 500000000) ≤ -Real.log (250000000000 / 483147504879) ∧
    -Real.log (250000000000 / 483147504879) ≤ (658861083 / 1000000000) := by
  have h := checkLog_sound (w := (233147504879 / 733147504879)) (n := 12)
    (lo := (329430541 / 500000000)) (hi := (658861083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483147504879 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483147504879 / 250000000000) = 1/(250000000000 / 483147504879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (329430541 / 500000000) (658861083 / 1000000000) (Real.log (483147504879 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (483147504879 / 250000000000) = -Real.log (250000000000 / 483147504879) := by
    rw [show ((483147504879 / 250000000000) : ℝ) = ((250000000000 / 483147504879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (659811307 / 1000000000) ≤ -Real.log (250000000000 / 483606821957) ∧
    -Real.log (250000000000 / 483606821957) ≤ (164952827 / 250000000) := by
  have h := checkLog_sound (w := (233606821957 / 733606821957)) (n := 12)
    (lo := (659811307 / 1000000000)) (hi := (164952827 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483606821957 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483606821957 / 250000000000) = 1/(250000000000 / 483606821957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (659811307 / 1000000000) (164952827 / 250000000) (Real.log (483606821957 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (483606821957 / 250000000000) = -Real.log (250000000000 / 483606821957) := by
    rw [show ((483606821957 / 250000000000) : ℝ) = ((250000000000 / 483606821957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (471213773 / 1000000000) ≤ -Real.log (250000000000 / 400484350647) ∧
    -Real.log (250000000000 / 400484350647) ≤ (235606887 / 500000000) := by
  have h := checkLog_sound (w := (150484350647 / 650484350647)) (n := 12)
    (lo := (471213773 / 1000000000)) (hi := (235606887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400484350647 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400484350647 / 250000000000) = 1/(250000000000 / 400484350647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (471213773 / 1000000000) (235606887 / 500000000) (Real.log (400484350647 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (400484350647 / 250000000000) = -Real.log (250000000000 / 400484350647) := by
    rw [show ((400484350647 / 250000000000) : ℝ) = ((250000000000 / 400484350647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (117977259 / 250000000) ≤ -Real.log (500000000000 / 801525778671) ∧
    -Real.log (500000000000 / 801525778671) ≤ (471909037 / 1000000000) := by
  have h := checkLog_sound (w := (301525778671 / 1301525778671)) (n := 12)
    (lo := (117977259 / 250000000)) (hi := (471909037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801525778671 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(801525778671 / 500000000000) = 1/(500000000000 / 801525778671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (117977259 / 250000000) (471909037 / 1000000000) (Real.log (801525778671 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (801525778671 / 500000000000) = -Real.log (500000000000 / 801525778671) := by
    rw [show ((801525778671 / 500000000000) : ℝ) = ((500000000000 / 801525778671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0395
