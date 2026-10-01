import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell203
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (19654283 / 62500000) ≤ -Real.log (1280 / 1753) ∧
    -Real.log (1280 / 1753) ≤ (314468529 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 3033)) (n := 12)
    (lo := (19654283 / 62500000)) (hi := (314468529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1753 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1753 / 1280) = 1/(1280 / 1753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (19654283 / 62500000) (314468529 / 1000000000) (Real.log (1753 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1753 / 1280) = -Real.log (1280 / 1753) := by
    rw [show ((1753 / 1280) : ℝ) = ((1280 / 1753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (57661461 / 125000000) ≤ -Real.log (807 / 1280) ∧
    -Real.log (807 / 1280) ≤ (461291689 / 1000000000) := by
  have h := checkLog_sound (w := (473 / 2087)) (n := 12)
    (lo := (57661461 / 125000000)) (hi := (461291689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 807) = 1/(807 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-461291689 / 1000000000) (-57661461 / 125000000) (Real.log (807 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (157020299 / 500000000) ≤ -Real.log (5120 / 7009) ∧
    -Real.log (5120 / 7009) ≤ (314040599 / 1000000000) := by
  have h := checkLog_sound (w := (1889 / 12129)) (n := 12)
    (lo := (157020299 / 500000000)) (hi := (314040599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7009 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7009 / 5120) = 1/(5120 / 7009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (157020299 / 500000000) (314040599 / 1000000000) (Real.log (7009 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7009 / 5120) = -Real.log (5120 / 7009) := by
    rw [show ((7009 / 5120) : ℝ) = ((5120 / 7009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (899146 / 1953125) ≤ -Real.log (3231 / 5120) ∧
    -Real.log (3231 / 5120) ≤ (460362753 / 1000000000) := by
  have h := checkLog_sound (w := (1889 / 8351)) (n := 12)
    (lo := (899146 / 1953125)) (hi := (460362753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3231) = 1/(3231 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-460362753 / 1000000000) (-899146 / 1953125) (Real.log (3231 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (233056653 / 1000000000) ≤ -Real.log (1000000 / 1262453) ∧
    -Real.log (1000000 / 1262453) ≤ (116528327 / 500000000) := by
  have h := checkLog_sound (w := (262453 / 2262453)) (n := 12)
    (lo := (233056653 / 1000000000)) (hi := (116528327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1262453 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1262453 / 1000000) = 1/(1000000 / 1262453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (233056653 / 1000000000) (116528327 / 500000000) (Real.log (1262453 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1262453 / 1000000) = -Real.log (1000000 / 1262453) := by
    rw [show ((1262453 / 1000000) : ℝ) = ((1000000 / 1262453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (304425463 / 1000000000) ≤ -Real.log (737547 / 1000000) ∧
    -Real.log (737547 / 1000000) ≤ (38053183 / 125000000) := by
  have h := checkLog_sound (w := (262453 / 1737547)) (n := 12)
    (lo := (304425463 / 1000000000)) (hi := (38053183 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 737547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 737547) = 1/(737547 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-38053183 / 125000000) (-304425463 / 1000000000) (Real.log (737547 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (233391659 / 1000000000) ≤ -Real.log (250000 / 315719) ∧
    -Real.log (250000 / 315719) ≤ (11669583 / 50000000) := by
  have h := checkLog_sound (w := (65719 / 565719)) (n := 12)
    (lo := (233391659 / 1000000000)) (hi := (11669583 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315719 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315719 / 250000) = 1/(250000 / 315719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (233391659 / 1000000000) (11669583 / 50000000) (Real.log (315719 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (315719 / 250000) = -Real.log (250000 / 315719) := by
    rw [show ((315719 / 250000) : ℝ) = ((250000 / 315719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (304999151 / 1000000000) ≤ -Real.log (184281 / 250000) ∧
    -Real.log (184281 / 250000) ≤ (19062447 / 62500000) := by
  have h := checkLog_sound (w := (65719 / 434281)) (n := 12)
    (lo := (304999151 / 1000000000)) (hi := (19062447 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 184281) = 1/(184281 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-19062447 / 62500000) (-304999151 / 1000000000) (Real.log (184281 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (43318521 / 250000000) ≤ -Real.log (125000 / 148649) ∧
    -Real.log (125000 / 148649) ≤ (34654817 / 200000000) := by
  have h := checkLog_sound (w := (23649 / 273649)) (n := 12)
    (lo := (43318521 / 250000000)) (hi := (34654817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148649 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148649 / 125000) = 1/(125000 / 148649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (43318521 / 250000000) (34654817 / 200000000) (Real.log (148649 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (148649 / 125000) = -Real.log (125000 / 148649) := by
    rw [show ((148649 / 125000) : ℝ) = ((125000 / 148649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (209723997 / 1000000000) ≤ -Real.log (101351 / 125000) ∧
    -Real.log (101351 / 125000) ≤ (104861999 / 500000000) := by
  have h := checkLog_sound (w := (23649 / 226351)) (n := 12)
    (lo := (209723997 / 1000000000)) (hi := (104861999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 101351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 101351) = 1/(101351 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-104861999 / 500000000) (-209723997 / 1000000000) (Real.log (101351 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (21692577 / 125000000) ≤ -Real.log (1000000 / 1189509) ∧
    -Real.log (1000000 / 1189509) ≤ (173540617 / 1000000000) := by
  have h := checkLog_sound (w := (189509 / 2189509)) (n := 12)
    (lo := (21692577 / 125000000)) (hi := (173540617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189509 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1189509 / 1000000) = 1/(1000000 / 1189509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (21692577 / 125000000) (173540617 / 1000000000) (Real.log (1189509 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1189509 / 1000000) = -Real.log (1000000 / 1189509) := by
    rw [show ((1189509 / 1000000) : ℝ) = ((1000000 / 1189509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (105057521 / 500000000) ≤ -Real.log (810491 / 1000000) ∧
    -Real.log (810491 / 1000000) ≤ (210115043 / 1000000000) := by
  have h := checkLog_sound (w := (189509 / 1810491)) (n := 12)
    (lo := (105057521 / 500000000)) (hi := (210115043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 810491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 810491) = 1/(810491 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-210115043 / 1000000000) (-105057521 / 500000000) (Real.log (810491 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (15488067 / 20000000) ≤ -Real.log (500000000000 / 1084648715567) ∧
    -Real.log (500000000000 / 1084648715567) ≤ (96800419 / 125000000) := by
  have h := checkLog_sound (w := (84648715567 / 2084648715567)) (n := 12)
    (lo := (8125617 / 100000000)) (hi := (81256171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084648715567 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1084648715567 / 1000000000000) = 1/(500000000000 / 1084648715567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (15488067 / 20000000) (96800419 / 125000000) (Real.log (1084648715567 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1084648715567 / 500000000000) = -Real.log (500000000000 / 1084648715567) := by
    rw [show ((1084648715567 / 500000000000) : ℝ) = ((500000000000 / 1084648715567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (96970027 / 125000000) ≤ -Real.log (500000000000 / 1086121437423) ∧
    -Real.log (500000000000 / 1086121437423) ≤ (387880109 / 500000000) := by
  have h := checkLog_sound (w := (86121437423 / 2086121437423)) (n := 12)
    (lo := (20653259 / 250000000)) (hi := (82613037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1086121437423 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1086121437423 / 1000000000000) = 1/(500000000000 / 1086121437423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (96970027 / 125000000) (387880109 / 500000000) (Real.log (1086121437423 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1086121437423 / 500000000000) = -Real.log (500000000000 / 1086121437423) := by
    rw [show ((1086121437423 / 500000000000) : ℝ) = ((500000000000 / 1086121437423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (537482117 / 1000000000) ≤ -Real.log (100000000000 / 171169159389) ∧
    -Real.log (100000000000 / 171169159389) ≤ (268741059 / 500000000) := by
  have h := checkLog_sound (w := (71169159389 / 271169159389)) (n := 12)
    (lo := (537482117 / 1000000000)) (hi := (268741059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171169159389 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171169159389 / 100000000000) = 1/(100000000000 / 171169159389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (537482117 / 1000000000) (268741059 / 500000000) (Real.log (171169159389 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (171169159389 / 100000000000) = -Real.log (100000000000 / 171169159389) := by
    rw [show ((171169159389 / 100000000000) : ℝ) = ((100000000000 / 171169159389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53839081 / 100000000) ≤ -Real.log (250000000000 / 428311925809) ∧
    -Real.log (250000000000 / 428311925809) ≤ (538390811 / 1000000000) := by
  have h := checkLog_sound (w := (178311925809 / 678311925809)) (n := 12)
    (lo := (53839081 / 100000000)) (hi := (538390811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((428311925809 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(428311925809 / 250000000000) = 1/(250000000000 / 428311925809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (53839081 / 100000000) (538390811 / 1000000000) (Real.log (428311925809 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (428311925809 / 250000000000) = -Real.log (250000000000 / 428311925809) := by
    rw [show ((428311925809 / 250000000000) : ℝ) = ((250000000000 / 428311925809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (191499041 / 500000000) ≤ -Real.log (500000000000 / 733337608903) ∧
    -Real.log (500000000000 / 733337608903) ≤ (382998083 / 1000000000) := by
  have h := checkLog_sound (w := (233337608903 / 1233337608903)) (n := 12)
    (lo := (191499041 / 500000000)) (hi := (382998083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733337608903 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733337608903 / 500000000000) = 1/(500000000000 / 733337608903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (191499041 / 500000000) (382998083 / 1000000000) (Real.log (733337608903 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (733337608903 / 500000000000) = -Real.log (500000000000 / 733337608903) := by
    rw [show ((733337608903 / 500000000000) : ℝ) = ((500000000000 / 733337608903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (383655659 / 1000000000) ≤ -Real.log (250000000000 / 366909996533) ∧
    -Real.log (250000000000 / 366909996533) ≤ (19182783 / 50000000) := by
  have h := checkLog_sound (w := (116909996533 / 616909996533)) (n := 12)
    (lo := (383655659 / 1000000000)) (hi := (19182783 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366909996533 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366909996533 / 250000000000) = 1/(250000000000 / 366909996533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (383655659 / 1000000000) (19182783 / 50000000) (Real.log (366909996533 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (366909996533 / 250000000000) = -Real.log (250000000000 / 366909996533) := by
    rw [show ((366909996533 / 250000000000) : ℝ) = ((250000000000 / 366909996533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1462977 / 40000000) ≤ -Real.log (964086338919 / 1000000000000) ∧
    -Real.log (964086338919 / 1000000000000) ≤ (18287213 / 500000000) := by
  have h := checkLog_sound (w := (35913661081 / 1964086338919)) (n := 12)
    (lo := (1462977 / 40000000)) (hi := (18287213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964086338919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964086338919) = 1/(964086338919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18287213 / 500000000) (-1462977 / 40000000) (Real.log (964086338919 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4556239 / 125000000) ≤ -Real.log (15065724799 / 15625000000) ∧
    -Real.log (15065724799 / 15625000000) ≤ (36449913 / 1000000000) := by
  have h := checkLog_sound (w := (559275201 / 30690724799)) (n := 12)
    (lo := (4556239 / 125000000)) (hi := (36449913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15065724799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15065724799) = 1/(15065724799 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-36449913 / 1000000000) (-4556239 / 125000000) (Real.log (15065724799 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell203
