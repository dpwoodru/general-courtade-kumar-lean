import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0049
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

theorem reflection_log_1_neg : (169788309 / 250000000) ≤ -Real.log (51200 / 100977) ∧
    -Real.log (51200 / 100977) ≤ (679153237 / 1000000000) := by
  have h := checkLog_sound (w := (49777 / 152177)) (n := 12)
    (lo := (169788309 / 250000000)) (hi := (679153237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100977 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100977 / 51200) = 1/(51200 / 100977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (169788309 / 250000000) (679153237 / 1000000000) (Real.log (100977 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100977 / 51200) = -Real.log (51200 / 100977) := by
    rw [show ((100977 / 51200) : ℝ) = ((51200 / 100977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (358297221 / 100000000) ≤ -Real.log (1423 / 51200) ∧
    -Real.log (1423 / 51200) ≤ (447871527 / 125000000) := by
  have h := checkLog_sound (w := (177 / 3023)) (n := 12)
    (lo := (11723631 / 100000000)) (hi := (117236311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1423) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1423) = 1/(1423 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-447871527 / 125000000) (-358297221 / 100000000) (Real.log (1423 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13581183 / 20000000) ≤ -Real.log (20480 / 40387) ∧
    -Real.log (20480 / 40387) ≤ (679059151 / 1000000000) := by
  have h := checkLog_sound (w := (19907 / 60867)) (n := 12)
    (lo := (13581183 / 20000000)) (hi := (679059151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40387 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40387 / 20480) = 1/(20480 / 40387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13581183 / 20000000) (679059151 / 1000000000) (Real.log (40387 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (40387 / 20480) = -Real.log (20480 / 40387) := by
    rw [show ((40387 / 20480) : ℝ) = ((20480 / 40387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3576318359 / 1000000000) ≤ -Real.log (573 / 20480) ∧
    -Real.log (573 / 20480) ≤ (715263673 / 200000000) := by
  have h := checkLog_sound (w := (67 / 1213)) (n := 12)
    (lo := (110582459 / 1000000000)) (hi := (5529123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 573) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 573) = 1/(573 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-715263673 / 200000000) (-3576318359 / 1000000000) (Real.log (573 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (332480339 / 500000000) ≤ -Real.log (25600 / 49777) ∧
    -Real.log (25600 / 49777) ≤ (664960679 / 1000000000) := by
  have h := checkLog_sound (w := (24177 / 75377)) (n := 12)
    (lo := (332480339 / 500000000)) (hi := (664960679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49777 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49777 / 25600) = 1/(25600 / 49777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (332480339 / 500000000) (664960679 / 1000000000) (Real.log (49777 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49777 / 25600) = -Real.log (25600 / 49777) := by
    rw [show ((49777 / 25600) : ℝ) = ((25600 / 49777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (288982503 / 100000000) ≤ -Real.log (1423 / 25600) ∧
    -Real.log (1423 / 25600) ≤ (577965007 / 200000000) := by
  have h := checkLog_sound (w := (177 / 3023)) (n := 12)
    (lo := (11723631 / 100000000)) (hi := (117236311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1423) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1423) = 1/(1423 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-577965007 / 200000000) (-288982503 / 100000000) (Real.log (1423 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (664769809 / 1000000000) ≤ -Real.log (10240 / 19907) ∧
    -Real.log (10240 / 19907) ≤ (66476981 / 100000000) := by
  have h := checkLog_sound (w := (9667 / 30147)) (n := 12)
    (lo := (664769809 / 1000000000)) (hi := (66476981 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19907 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19907 / 10240) = 1/(10240 / 19907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (664769809 / 1000000000) (66476981 / 100000000) (Real.log (19907 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (19907 / 10240) = -Real.log (10240 / 19907) := by
    rw [show ((19907 / 10240) : ℝ) = ((10240 / 19907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2883171179 / 1000000000) ≤ -Real.log (573 / 10240) ∧
    -Real.log (573 / 10240) ≤ (180198199 / 62500000) := by
  have h := checkLog_sound (w := (67 / 1213)) (n := 12)
    (lo := (110582459 / 1000000000)) (hi := (5529123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 573) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 573) = 1/(573 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-180198199 / 62500000) (-2883171179 / 1000000000) (Real.log (573 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (681344299 / 1000000000) ≤ -Real.log (1000000 / 1976533) ∧
    -Real.log (1000000 / 1976533) ≤ (6813443 / 10000000) := by
  have h := checkLog_sound (w := (976533 / 2976533)) (n := 12)
    (lo := (681344299 / 1000000000)) (hi := (6813443 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976533 / 1000000) = 1/(1000000 / 1976533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (681344299 / 1000000000) (6813443 / 10000000) (Real.log (1976533 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1976533 / 1000000) = -Real.log (1000000 / 1976533) := by
    rw [show ((1976533 / 1000000) : ℝ) = ((1000000 / 1976533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3752160097 / 1000000000) ≤ -Real.log (23467 / 1000000) ∧
    -Real.log (23467 / 1000000) ≤ (3752160103 / 1000000000) := by
  have h := checkLog_sound (w := (7783 / 54717)) (n := 12)
    (lo := (286424197 / 1000000000)) (hi := (143212099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23467) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23467) = 1/(23467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3752160103 / 1000000000) (-3752160097 / 1000000000) (Real.log (23467 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (681420187 / 1000000000) ≤ -Real.log (1000000 / 1976683) ∧
    -Real.log (1000000 / 1976683) ≤ (170355047 / 250000000) := by
  have h := checkLog_sound (w := (976683 / 2976683)) (n := 12)
    (lo := (681420187 / 1000000000)) (hi := (170355047 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976683 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976683 / 1000000) = 1/(1000000 / 1976683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (681420187 / 1000000000) (170355047 / 250000000) (Real.log (1976683 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1976683 / 1000000) = -Real.log (1000000 / 1976683) := by
    rw [show ((1976683 / 1000000) : ℝ) = ((1000000 / 1976683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3758572567 / 1000000000) ≤ -Real.log (23317 / 1000000) ∧
    -Real.log (23317 / 1000000) ≤ (3758572573 / 1000000000) := by
  have h := checkLog_sound (w := (7933 / 54567)) (n := 12)
    (lo := (292836667 / 1000000000)) (hi := (73209167 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23317) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23317) = 1/(23317 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3758572573 / 1000000000) (-3758572567 / 1000000000) (Real.log (23317 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (27251141 / 40000000) ≤ -Real.log (1000000 / 1976403) ∧
    -Real.log (1000000 / 1976403) ≤ (340639263 / 500000000) := by
  have h := checkLog_sound (w := (976403 / 2976403)) (n := 12)
    (lo := (27251141 / 40000000)) (hi := (340639263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976403 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976403 / 1000000) = 1/(1000000 / 1976403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (27251141 / 40000000) (340639263 / 500000000) (Real.log (1976403 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1976403 / 1000000) = -Real.log (1000000 / 1976403) := by
    rw [show ((1976403 / 1000000) : ℝ) = ((1000000 / 1976403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (374663569 / 100000000) ≤ -Real.log (23597 / 1000000) ∧
    -Real.log (23597 / 1000000) ≤ (234164731 / 62500000) := by
  have h := checkLog_sound (w := (7653 / 54847)) (n := 12)
    (lo := (28089979 / 100000000)) (hi := (280899791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23597) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23597) = 1/(23597 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-234164731 / 62500000) (-374663569 / 100000000) (Real.log (23597 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (68135543 / 100000000) ≤ -Real.log (200000 / 395311) ∧
    -Real.log (200000 / 395311) ≤ (681355431 / 1000000000) := by
  have h := checkLog_sound (w := (195311 / 595311)) (n := 12)
    (lo := (68135543 / 100000000)) (hi := (681355431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395311 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395311 / 200000) = 1/(200000 / 395311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (68135543 / 100000000) (681355431 / 1000000000) (Real.log (395311 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (395311 / 200000) = -Real.log (200000 / 395311) := by
    rw [show ((395311 / 200000) : ℝ) = ((200000 / 395311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3753098023 / 1000000000) ≤ -Real.log (4689 / 200000) ∧
    -Real.log (4689 / 200000) ≤ (3753098029 / 1000000000) := by
  have h := checkLog_sound (w := (1561 / 10939)) (n := 12)
    (lo := (287362123 / 1000000000)) (hi := (71840531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4689) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 4689) = 1/(4689 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3753098029 / 1000000000) (-3753098023 / 1000000000) (Real.log (4689 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1108376099 / 250000000) ≤ -Real.log (500000000000 / 42113031064899) ∧
    -Real.log (500000000000 / 42113031064899) ≤ (4433504403 / 1000000000) := by
  have h := checkLog_sound (w := (10113031064899 / 74113031064899)) (n := 12)
    (lo := (68655329 / 250000000)) (hi := (274621317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42113031064899 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(42113031064899 / 32000000000000) = 1/(500000000000 / 42113031064899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1108376099 / 250000000) (4433504403 / 1000000000) (Real.log (42113031064899 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (42113031064899 / 500000000000) = -Real.log (500000000000 / 42113031064899) := by
    rw [show ((42113031064899 / 500000000000) : ℝ) = ((500000000000 / 42113031064899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2219996377 / 500000000) ≤ -Real.log (250000000000 / 21193581935927) ∧
    -Real.log (250000000000 / 21193581935927) ≤ (4439992761 / 1000000000) := by
  have h := checkLog_sound (w := (5193581935927 / 37193581935927)) (n := 12)
    (lo := (140554837 / 500000000)) (hi := (11244387 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21193581935927 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(21193581935927 / 16000000000000) = 1/(250000000000 / 21193581935927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2219996377 / 500000000) (4439992761 / 1000000000) (Real.log (21193581935927 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (21193581935927 / 250000000000) = -Real.log (250000000000 / 21193581935927) := by
    rw [show ((21193581935927 / 250000000000) : ℝ) = ((250000000000 / 21193581935927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (553489277 / 125000000) ≤ -Real.log (31250000000 / 2617391776497) ∧
    -Real.log (31250000000 / 2617391776497) ≤ (4427914223 / 1000000000) := by
  have h := checkLog_sound (w := (617391776497 / 4617391776497)) (n := 12)
    (lo := (8407223 / 31250000)) (hi := (269031137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2617391776497 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2617391776497 / 2000000000000) = 1/(31250000000 / 2617391776497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (553489277 / 125000000) (4427914223 / 1000000000) (Real.log (2617391776497 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2617391776497 / 31250000000) = -Real.log (31250000000 / 2617391776497) := by
    rw [show ((2617391776497 / 31250000000) : ℝ) = ((31250000000 / 2617391776497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4434453453 / 1000000000) ≤ -Real.log (500000000000 / 42153017701003) ∧
    -Real.log (500000000000 / 42153017701003) ≤ (221722673 / 50000000) := by
  have h := checkLog_sound (w := (10153017701003 / 74153017701003)) (n := 12)
    (lo := (275570373 / 1000000000)) (hi := (137785187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42153017701003 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(42153017701003 / 32000000000000) = 1/(500000000000 / 42153017701003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4434453453 / 1000000000) (221722673 / 50000000) (Real.log (42153017701003 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (42153017701003 / 500000000000) = -Real.log (500000000000 / 42153017701003) := by
    rw [show ((42153017701003 / 500000000000) : ℝ) = ((500000000000 / 42153017701003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0049
