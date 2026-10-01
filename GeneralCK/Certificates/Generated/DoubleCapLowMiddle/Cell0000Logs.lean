import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0000
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

theorem reflection_log_1_neg : (170774211 / 250000000) ≤ -Real.log (50 / 99) ∧
    -Real.log (50 / 99) ≤ (136619369 / 200000000) := by
  have h := checkLog_sound (w := (49 / 149)) (n := 12)
    (lo := (170774211 / 250000000)) (hi := (136619369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99 / 50) = 1/(50 / 99) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170774211 / 250000000) (136619369 / 200000000) (Real.log (99 / 50)) := by
  have h := reflection_log_1_neg
  have he : Real.log (99 / 50) = -Real.log (50 / 99) := by
    rw [show ((99 / 50) : ℝ) = ((50 / 99) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1956011501 / 500000000) ≤ -Real.log (1 / 50) ∧
    -Real.log (1 / 50) ≤ (122250719 / 31250000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25 / 16) = 1/(1 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-122250719 / 31250000) (-1956011501 / 500000000) (Real.log (1 / 50)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (170762497 / 250000000) ≤ -Real.log (500000000000 / 989953613281) ∧
    -Real.log (500000000000 / 989953613281) ≤ (683049989 / 1000000000) := by
  have h := checkLog_sound (w := (489953613281 / 1489953613281)) (n := 12)
    (lo := (170762497 / 250000000)) (hi := (683049989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989953613281 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989953613281 / 500000000000) = 1/(500000000000 / 989953613281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (170762497 / 250000000) (683049989 / 1000000000) (Real.log (989953613281 / 500000000000)) := by
  have h := reflection_log_3_neg
  have he : Real.log (989953613281 / 500000000000) = -Real.log (500000000000 / 989953613281) := by
    rw [show ((989953613281 / 500000000000) : ℝ) = ((500000000000 / 989953613281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (244212191 / 62500000) ≤ -Real.log (10046386719 / 500000000000) ∧
    -Real.log (10046386719 / 500000000000) ≤ (1953697531 / 500000000) := by
  have h := checkLog_sound (w := (5578613281 / 25671386719)) (n := 12)
    (lo := (110414789 / 250000000)) (hi := (441659157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 10046386719) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625000000 / 10046386719) = 1/(10046386719 / 500000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1953697531 / 500000000) (-244212191 / 62500000) (Real.log (10046386719 / 500000000000)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (672944473 / 1000000000) ≤ -Real.log (25 / 49) ∧
    -Real.log (25 / 49) ≤ (336472237 / 500000000) := by
  have h := checkLog_sound (w := (12 / 37)) (n := 12)
    (lo := (672944473 / 1000000000)) (hi := (336472237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49 / 25) = 1/(25 / 49) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (672944473 / 1000000000) (336472237 / 500000000) (Real.log (49 / 25)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49 / 25) = -Real.log (25 / 49) := by
    rw [show ((49 / 25) : ℝ) = ((25 / 49) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1609437911 / 500000000) ≤ -Real.log (1 / 25) ∧
    -Real.log (1 / 25) ≤ (3218875827 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(25 / 16) = 1/(1 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3218875827 / 1000000000) (-1609437911 / 500000000) (Real.log (1 / 25)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (672849801 / 1000000000) ≤ -Real.log (20480 / 40137) ∧
    -Real.log (20480 / 40137) ≤ (336424901 / 500000000) := by
  have h := checkLog_sound (w := (19657 / 60617)) (n := 12)
    (lo := (672849801 / 1000000000)) (hi := (336424901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40137 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40137 / 20480) = 1/(20480 / 40137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (672849801 / 1000000000) (336424901 / 500000000) (Real.log (40137 / 20480)) := by
  have h := reflection_log_7_neg
  have he : Real.log (40137 / 20480) = -Real.log (20480 / 40137) := by
    rw [show ((40137 / 20480) : ℝ) = ((20480 / 40137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (803561969 / 250000000) ≤ -Real.log (823 / 20480) ∧
    -Real.log (823 / 20480) ≤ (3214247881 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 2103)) (n := 12)
    (lo := (110414789 / 250000000)) (hi := (441659157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 823) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1280 / 823) = 1/(823 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3214247881 / 1000000000) (-803561969 / 250000000) (Real.log (823 / 20480)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684565967 / 1000000000) ≤ -Real.log (1000000 / 1982911) ∧
    -Real.log (1000000 / 1982911) ≤ (42785373 / 62500000) := by
  have h := checkLog_sound (w := (982911 / 2982911)) (n := 12)
    (lo := (684565967 / 1000000000)) (hi := (42785373 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982911 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982911 / 1000000) = 1/(1000000 / 1982911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684565967 / 1000000000) (42785373 / 62500000) (Real.log (1982911 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1982911 / 1000000) = -Real.log (1000000 / 1982911) := by
    rw [show ((1982911 / 1000000) : ℝ) = ((1000000 / 1982911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2034660147 / 500000000) ≤ -Real.log (17089 / 1000000) ∧
    -Real.log (17089 / 1000000) ≤ (40693203 / 10000000) := by
  have h := checkLog_sound (w := (14161 / 48339)) (n := 12)
    (lo := (301792197 / 500000000)) (hi := (120716879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17089) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17089) = 1/(17089 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-40693203 / 10000000) (-2034660147 / 500000000) (Real.log (17089 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (342302399 / 500000000) ≤ -Real.log (250000 / 495747) ∧
    -Real.log (250000 / 495747) ≤ (684604799 / 1000000000) := by
  have h := checkLog_sound (w := (245747 / 745747)) (n := 12)
    (lo := (342302399 / 500000000)) (hi := (684604799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495747 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495747 / 250000) = 1/(250000 / 495747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (342302399 / 500000000) (684604799 / 1000000000) (Real.log (495747 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (495747 / 250000) = -Real.log (250000 / 495747) := by
    rw [show ((495747 / 250000) : ℝ) = ((250000 / 495747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2036918149 / 500000000) ≤ -Real.log (4253 / 250000) ∧
    -Real.log (4253 / 250000) ≤ (254614769 / 62500000) := by
  have h := checkLog_sound (w := (7119 / 24131)) (n := 12)
    (lo := (304050199 / 500000000)) (hi := (608100399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8506) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8506) = 1/(4253 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-254614769 / 62500000) (-2036918149 / 500000000) (Real.log (4253 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (684534699 / 1000000000) ≤ -Real.log (1000000 / 1982849) ∧
    -Real.log (1000000 / 1982849) ≤ (6845347 / 10000000) := by
  have h := checkLog_sound (w := (982849 / 2982849)) (n := 12)
    (lo := (684534699 / 1000000000)) (hi := (6845347 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982849 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982849 / 1000000) = 1/(1000000 / 1982849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (684534699 / 1000000000) (6845347 / 10000000) (Real.log (1982849 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1982849 / 1000000) = -Real.log (1000000 / 1982849) := by
    rw [show ((1982849 / 1000000) : ℝ) = ((1000000 / 1982849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (813139759 / 200000000) ≤ -Real.log (17151 / 1000000) ∧
    -Real.log (17151 / 1000000) ≤ (4065698801 / 1000000000) := by
  have h := checkLog_sound (w := (14099 / 48401)) (n := 12)
    (lo := (119992579 / 200000000)) (hi := (37497681 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17151) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17151) = 1/(17151 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4065698801 / 1000000000) (-813139759 / 200000000) (Real.log (17151 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684573531 / 1000000000) ≤ -Real.log (500000 / 991463) ∧
    -Real.log (500000 / 991463) ≤ (171143383 / 250000000) := by
  have h := checkLog_sound (w := (491463 / 1491463)) (n := 12)
    (lo := (684573531 / 1000000000)) (hi := (171143383 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991463 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991463 / 500000) = 1/(500000 / 991463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684573531 / 1000000000) (171143383 / 250000000) (Real.log (991463 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (991463 / 500000) = -Real.log (500000 / 991463) := by
    rw [show ((991463 / 500000) : ℝ) = ((500000 / 991463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4070198437 / 1000000000) ≤ -Real.log (8537 / 500000) ∧
    -Real.log (8537 / 500000) ≤ (4070198443 / 1000000000) := by
  have h := checkLog_sound (w := (3544 / 12081)) (n := 12)
    (lo := (604462537 / 1000000000)) (hi := (302231269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8537) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8537) = 1/(8537 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-4070198443 / 1000000000) (-4070198437 / 1000000000) (Real.log (8537 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (237694313 / 50000000) ≤ -Real.log (500000000000 / 58017174790801) ∧
    -Real.log (500000000000 / 58017174790801) ≤ (4753886267 / 1000000000) := by
  have h := checkLog_sound (w := (26017174790801 / 90017174790801)) (n := 12)
    (lo := (29750159 / 50000000)) (hi := (595003181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58017174790801 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(58017174790801 / 32000000000000) = 1/(500000000000 / 58017174790801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (237694313 / 50000000) (4753886267 / 1000000000) (Real.log (58017174790801 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (58017174790801 / 500000000000) = -Real.log (500000000000 / 58017174790801) := by
    rw [show ((58017174790801 / 500000000000) : ℝ) = ((500000000000 / 58017174790801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (594805137 / 125000000) ≤ -Real.log (100000000000 / 11656407241947) ∧
    -Real.log (100000000000 / 11656407241947) ≤ (4758441103 / 1000000000) := by
  have h := checkLog_sound (w := (5256407241947 / 18056407241947)) (n := 12)
    (lo := (4684047 / 7812500)) (hi := (599558017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11656407241947 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11656407241947 / 6400000000000) = 1/(100000000000 / 11656407241947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (594805137 / 125000000) (4758441103 / 1000000000) (Real.log (11656407241947 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11656407241947 / 100000000000) = -Real.log (100000000000 / 11656407241947) := by
    rw [show ((11656407241947 / 100000000000) : ℝ) = ((100000000000 / 11656407241947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2375116747 / 500000000) ≤ -Real.log (500000000000 / 57805638155209) ∧
    -Real.log (500000000000 / 57805638155209) ≤ (4750233501 / 1000000000) := by
  have h := checkLog_sound (w := (25805638155209 / 89805638155209)) (n := 12)
    (lo := (295675207 / 500000000)) (hi := (118270083 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57805638155209 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(57805638155209 / 32000000000000) = 1/(500000000000 / 57805638155209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2375116747 / 500000000) (4750233501 / 1000000000) (Real.log (57805638155209 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (57805638155209 / 500000000000) = -Real.log (500000000000 / 57805638155209) := by
    rw [show ((57805638155209 / 500000000000) : ℝ) = ((500000000000 / 57805638155209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (9286664 / 1953125) ≤ -Real.log (125000000000 / 14517145952911) ∧
    -Real.log (125000000000 / 14517145952911) ≤ (190190879 / 40000000) := by
  have h := checkLog_sound (w := (6517145952911 / 22517145952911)) (n := 12)
    (lo := (74486111 / 125000000)) (hi := (595888889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14517145952911 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(14517145952911 / 8000000000000) = 1/(125000000000 / 14517145952911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (9286664 / 1953125) (190190879 / 40000000) (Real.log (14517145952911 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (14517145952911 / 125000000000) = -Real.log (125000000000 / 14517145952911) := by
    rw [show ((14517145952911 / 125000000000) : ℝ) = ((125000000000 / 14517145952911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0000
