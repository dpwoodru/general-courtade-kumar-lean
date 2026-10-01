import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0093
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

theorem reflection_log_1_neg : (672735187 / 1000000000) ≤ -Real.log (51200 / 100331) ∧
    -Real.log (51200 / 100331) ≤ (168183797 / 250000000) := by
  have h := checkLog_sound (w := (49131 / 151531)) (n := 12)
    (lo := (672735187 / 1000000000)) (hi := (168183797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100331 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100331 / 51200) = 1/(51200 / 100331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (672735187 / 1000000000) (168183797 / 250000000) (Real.log (100331 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100331 / 51200) = -Real.log (51200 / 100331) := by
    rw [show ((100331 / 51200) : ℝ) = ((51200 / 100331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3208674131 / 1000000000) ≤ -Real.log (2069 / 51200) ∧
    -Real.log (2069 / 51200) ≤ (401084267 / 125000000) := by
  have h := checkLog_sound (w := (1131 / 5269)) (n := 12)
    (lo := (436085411 / 1000000000)) (hi := (109021353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2069) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2069) = 1/(2069 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-401084267 / 125000000) (-3208674131 / 1000000000) (Real.log (2069 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (168136449 / 250000000) ≤ -Real.log (6400 / 12539) ∧
    -Real.log (6400 / 12539) ≤ (672545797 / 1000000000) := by
  have h := checkLog_sound (w := (6139 / 18939)) (n := 12)
    (lo := (168136449 / 250000000)) (hi := (672545797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12539 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12539 / 6400) = 1/(6400 / 12539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (168136449 / 250000000) (672545797 / 1000000000) (Real.log (12539 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12539 / 6400) = -Real.log (6400 / 12539) := by
    rw [show ((12539 / 6400) : ℝ) = ((6400 / 12539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3199532859 / 1000000000) ≤ -Real.log (261 / 6400) ∧
    -Real.log (261 / 6400) ≤ (49992701 / 15625000) := by
  have h := checkLog_sound (w := (139 / 661)) (n := 12)
    (lo := (426944139 / 1000000000)) (hi := (21347207 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 261) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 261) = 1/(261 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-49992701 / 15625000) (-3199532859 / 1000000000) (Real.log (261 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (81487231 / 125000000) ≤ -Real.log (25600 / 49131) ∧
    -Real.log (25600 / 49131) ≤ (651897849 / 1000000000) := by
  have h := checkLog_sound (w := (23531 / 74731)) (n := 12)
    (lo := (81487231 / 125000000)) (hi := (651897849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49131 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49131 / 25600) = 1/(25600 / 49131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (81487231 / 125000000) (651897849 / 1000000000) (Real.log (49131 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49131 / 25600) = -Real.log (25600 / 49131) := by
    rw [show ((49131 / 25600) : ℝ) = ((25600 / 49131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2515526951 / 1000000000) ≤ -Real.log (2069 / 25600) ∧
    -Real.log (2069 / 25600) ≤ (503105391 / 200000000) := by
  have h := checkLog_sound (w := (1131 / 5269)) (n := 12)
    (lo := (436085411 / 1000000000)) (hi := (109021353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2069) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2069) = 1/(2069 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-503105391 / 200000000) (-2515526951 / 1000000000) (Real.log (2069 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (162877763 / 250000000) ≤ -Real.log (3200 / 6139) ∧
    -Real.log (3200 / 6139) ≤ (651511053 / 1000000000) := by
  have h := checkLog_sound (w := (2939 / 9339)) (n := 12)
    (lo := (162877763 / 250000000)) (hi := (651511053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6139 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6139 / 3200) = 1/(3200 / 6139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (162877763 / 250000000) (651511053 / 1000000000) (Real.log (6139 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (6139 / 3200) = -Real.log (3200 / 6139) := by
    rw [show ((6139 / 3200) : ℝ) = ((3200 / 6139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2506385679 / 1000000000) ≤ -Real.log (261 / 3200) ∧
    -Real.log (261 / 3200) ≤ (2506385683 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 661)) (n := 12)
    (lo := (426944139 / 1000000000)) (hi := (21347207 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 261) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 261) = 1/(261 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2506385683 / 1000000000) (-2506385679 / 1000000000) (Real.log (261 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (676228869 / 1000000000) ≤ -Real.log (62500 / 122903) ∧
    -Real.log (62500 / 122903) ≤ (67622887 / 100000000) := by
  have h := checkLog_sound (w := (60403 / 185403)) (n := 12)
    (lo := (676228869 / 1000000000)) (hi := (67622887 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122903 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122903 / 62500) = 1/(62500 / 122903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (676228869 / 1000000000) (67622887 / 100000000) (Real.log (122903 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (122903 / 62500) = -Real.log (62500 / 122903) := by
    rw [show ((122903 / 62500) : ℝ) = ((62500 / 122903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1697329401 / 500000000) ≤ -Real.log (2097 / 62500) ∧
    -Real.log (2097 / 62500) ≤ (3394658807 / 1000000000) := by
  have h := checkLog_sound (w := (7237 / 24013)) (n := 12)
    (lo := (311035041 / 500000000)) (hi := (622070083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8388) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8388) = 1/(2097 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3394658807 / 1000000000) (-1697329401 / 500000000) (Real.log (2097 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42273489 / 62500000) ≤ -Real.log (1000000 / 1966737) ∧
    -Real.log (1000000 / 1966737) ≤ (27055033 / 40000000) := by
  have h := checkLog_sound (w := (966737 / 2966737)) (n := 12)
    (lo := (42273489 / 62500000)) (hi := (27055033 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1966737 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1966737 / 1000000) = 1/(1000000 / 1966737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42273489 / 62500000) (27055033 / 40000000) (Real.log (1966737 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1966737 / 1000000) = -Real.log (1000000 / 1966737) := by
    rw [show ((1966737 / 1000000) : ℝ) = ((1000000 / 1966737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (425413701 / 125000000) ≤ -Real.log (33263 / 1000000) ∧
    -Real.log (33263 / 1000000) ≤ (3403309613 / 1000000000) := by
  have h := checkLog_sound (w := (29237 / 95763)) (n := 12)
    (lo := (78840111 / 125000000)) (hi := (630720889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33263) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 33263) = 1/(33263 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3403309613 / 1000000000) (-425413701 / 125000000) (Real.log (33263 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (676075281 / 1000000000) ≤ -Real.log (500000 / 983073) ∧
    -Real.log (500000 / 983073) ≤ (338037641 / 500000000) := by
  have h := checkLog_sound (w := (483073 / 1483073)) (n := 12)
    (lo := (676075281 / 1000000000)) (hi := (338037641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983073 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983073 / 500000) = 1/(500000 / 983073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (676075281 / 1000000000) (338037641 / 500000000) (Real.log (983073 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (983073 / 500000) = -Real.log (500000 / 983073) := by
    rw [show ((983073 / 500000) : ℝ) = ((500000 / 983073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (677139623 / 200000000) ≤ -Real.log (16927 / 500000) ∧
    -Real.log (16927 / 500000) ≤ (84642453 / 25000000) := by
  have h := checkLog_sound (w := (14323 / 48177)) (n := 12)
    (lo := (122621879 / 200000000)) (hi := (153277349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16927) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16927) = 1/(16927 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-84642453 / 25000000) (-677139623 / 200000000) (Real.log (16927 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (676225309 / 1000000000) ≤ -Real.log (1000000 / 1966441) ∧
    -Real.log (1000000 / 1966441) ≤ (67622531 / 100000000) := by
  have h := checkLog_sound (w := (966441 / 2966441)) (n := 12)
    (lo := (676225309 / 1000000000)) (hi := (67622531 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1966441 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1966441 / 1000000) = 1/(1000000 / 1966441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (676225309 / 1000000000) (67622531 / 100000000) (Real.log (1966441 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1966441 / 1000000) = -Real.log (1000000 / 1966441) := by
    rw [show ((1966441 / 1000000) : ℝ) = ((1000000 / 1966441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (212153137 / 62500000) ≤ -Real.log (33559 / 1000000) ∧
    -Real.log (33559 / 1000000) ≤ (3394450197 / 1000000000) := by
  have h := checkLog_sound (w := (28941 / 96059)) (n := 12)
    (lo := (19433171 / 31250000)) (hi := (621861473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33559) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 33559) = 1/(33559 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3394450197 / 1000000000) (-212153137 / 62500000) (Real.log (33559 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4070887671 / 1000000000) ≤ -Real.log (250000000000 / 14652241297091) ∧
    -Real.log (250000000000 / 14652241297091) ≤ (4070887677 / 1000000000) := by
  have h := checkLog_sound (w := (6652241297091 / 22652241297091)) (n := 12)
    (lo := (605151771 / 1000000000)) (hi := (151287943 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14652241297091 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(14652241297091 / 8000000000000) = 1/(250000000000 / 14652241297091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4070887671 / 1000000000) (4070887677 / 1000000000) (Real.log (14652241297091 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (14652241297091 / 250000000000) = -Real.log (250000000000 / 14652241297091) := by
    rw [show ((14652241297091 / 250000000000) : ℝ) = ((250000000000 / 14652241297091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (509960679 / 125000000) ≤ -Real.log (250000000000 / 14781716922707) ∧
    -Real.log (250000000000 / 14781716922707) ≤ (2039842719 / 500000000) := by
  have h := checkLog_sound (w := (6781716922707 / 22781716922707)) (n := 12)
    (lo := (153487383 / 250000000)) (hi := (613949533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14781716922707 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(14781716922707 / 8000000000000) = 1/(250000000000 / 14781716922707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (509960679 / 125000000) (2039842719 / 500000000) (Real.log (14781716922707 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14781716922707 / 250000000000) = -Real.log (250000000000 / 14781716922707) := by
    rw [show ((14781716922707 / 250000000000) : ℝ) = ((250000000000 / 14781716922707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1015443349 / 250000000) ≤ -Real.log (100000000000 / 5807721391859) ∧
    -Real.log (100000000000 / 5807721391859) ≤ (2030886701 / 500000000) := by
  have h := checkLog_sound (w := (2607721391859 / 9007721391859)) (n := 12)
    (lo := (74504687 / 125000000)) (hi := (596037497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5807721391859 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5807721391859 / 3200000000000) = 1/(100000000000 / 5807721391859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1015443349 / 250000000) (2030886701 / 500000000) (Real.log (5807721391859 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5807721391859 / 100000000000) = -Real.log (100000000000 / 5807721391859) := by
    rw [show ((5807721391859 / 100000000000) : ℝ) = ((100000000000 / 5807721391859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2035337751 / 500000000) ≤ -Real.log (250000000000 / 14649132870467) ∧
    -Real.log (250000000000 / 14649132870467) ≤ (1017668877 / 250000000) := by
  have h := checkLog_sound (w := (6649132870467 / 22649132870467)) (n := 12)
    (lo := (302469801 / 500000000)) (hi := (604939603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14649132870467 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(14649132870467 / 8000000000000) = 1/(250000000000 / 14649132870467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2035337751 / 500000000) (1017668877 / 250000000) (Real.log (14649132870467 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (14649132870467 / 250000000000) = -Real.log (250000000000 / 14649132870467) := by
    rw [show ((14649132870467 / 250000000000) : ℝ) = ((250000000000 / 14649132870467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0093
