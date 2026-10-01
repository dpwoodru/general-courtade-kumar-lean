import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0048
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

theorem reflection_log_1_neg : (42452957 / 62500000) ≤ -Real.log (102400 / 201973) ∧
    -Real.log (102400 / 201973) ≤ (679247313 / 1000000000) := by
  have h := checkLog_sound (w := (99573 / 304373)) (n := 12)
    (lo := (42452957 / 62500000)) (hi := (679247313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201973 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201973 / 102400) = 1/(102400 / 201973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (42452957 / 62500000) (679247313 / 1000000000) (Real.log (201973 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201973 / 102400) = -Real.log (102400 / 201973) := by
    rw [show ((201973 / 102400) : ℝ) = ((102400 / 201973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3589670631 / 1000000000) ≤ -Real.log (2827 / 102400) ∧
    -Real.log (2827 / 102400) ≤ (3589670637 / 1000000000) := by
  have h := checkLog_sound (w := (373 / 6027)) (n := 12)
    (lo := (123934731 / 1000000000)) (hi := (30983683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2827) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2827) = 1/(2827 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3589670637 / 1000000000) (-3589670631 / 1000000000) (Real.log (2827 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (169788309 / 250000000) ≤ -Real.log (51200 / 100977) ∧
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


theorem reflection_log_3 : Bounds (169788309 / 250000000) (679153237 / 1000000000) (Real.log (100977 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100977 / 51200) = -Real.log (51200 / 100977) := by
    rw [show ((100977 / 51200) : ℝ) = ((51200 / 100977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (358297221 / 100000000) ≤ -Real.log (1423 / 51200) ∧
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


theorem reflection_log_4 : Bounds (-447871527 / 125000000) (-358297221 / 100000000) (Real.log (1423 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (665151511 / 1000000000) ≤ -Real.log (51200 / 99573) ∧
    -Real.log (51200 / 99573) ≤ (83143939 / 125000000) := by
  have h := checkLog_sound (w := (48373 / 150773)) (n := 12)
    (lo := (665151511 / 1000000000)) (hi := (83143939 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99573 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99573 / 51200) = 1/(51200 / 99573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (665151511 / 1000000000) (83143939 / 125000000) (Real.log (99573 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99573 / 51200) = -Real.log (51200 / 99573) := by
    rw [show ((99573 / 51200) : ℝ) = ((51200 / 99573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2896523451 / 1000000000) ≤ -Real.log (2827 / 51200) ∧
    -Real.log (2827 / 51200) ≤ (45258179 / 15625000) := by
  have h := checkLog_sound (w := (373 / 6027)) (n := 12)
    (lo := (123934731 / 1000000000)) (hi := (30983683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2827) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2827) = 1/(2827 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-45258179 / 15625000) (-2896523451 / 1000000000) (Real.log (2827 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (332480339 / 500000000) ≤ -Real.log (25600 / 49777) ∧
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


theorem reflection_log_7 : Bounds (332480339 / 500000000) (664960679 / 1000000000) (Real.log (49777 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49777 / 25600) = -Real.log (25600 / 49777) := by
    rw [show ((49777 / 25600) : ℝ) = ((25600 / 49777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (288982503 / 100000000) ≤ -Real.log (1423 / 25600) ∧
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


theorem reflection_log_8 : Bounds (-577965007 / 200000000) (-288982503 / 100000000) (Real.log (1423 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (681419681 / 1000000000) ≤ -Real.log (500000 / 988341) ∧
    -Real.log (500000 / 988341) ≤ (340709841 / 500000000) := by
  have h := checkLog_sound (w := (488341 / 1488341)) (n := 12)
    (lo := (681419681 / 1000000000)) (hi := (340709841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988341 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988341 / 500000) = 1/(500000 / 988341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (681419681 / 1000000000) (340709841 / 500000000) (Real.log (988341 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (988341 / 500000) = -Real.log (500000 / 988341) := by
    rw [show ((988341 / 500000) : ℝ) = ((500000 / 988341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3758529681 / 1000000000) ≤ -Real.log (11659 / 500000) ∧
    -Real.log (11659 / 500000) ≤ (3758529687 / 1000000000) := by
  have h := checkLog_sound (w := (1983 / 13642)) (n := 12)
    (lo := (292793781 / 1000000000)) (hi := (146396891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11659) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11659) = 1/(11659 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3758529687 / 1000000000) (-3758529681 / 1000000000) (Real.log (11659 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (681495057 / 1000000000) ≤ -Real.log (1000000 / 1976831) ∧
    -Real.log (1000000 / 1976831) ≤ (340747529 / 500000000) := by
  have h := checkLog_sound (w := (976831 / 2976831)) (n := 12)
    (lo := (681495057 / 1000000000)) (hi := (340747529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976831 / 1000000) = 1/(1000000 / 1976831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (681495057 / 1000000000) (340747529 / 500000000) (Real.log (1976831 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1976831 / 1000000) = -Real.log (1000000 / 1976831) := by
    rw [show ((1976831 / 1000000) : ℝ) = ((1000000 / 1976831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3764940097 / 1000000000) ≤ -Real.log (23169 / 1000000) ∧
    -Real.log (23169 / 1000000) ≤ (3764940103 / 1000000000) := by
  have h := checkLog_sound (w := (8081 / 54419)) (n := 12)
    (lo := (299204197 / 1000000000)) (hi := (149602099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23169) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23169) = 1/(23169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3764940103 / 1000000000) (-3764940097 / 1000000000) (Real.log (23169 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (170338731 / 250000000) ≤ -Real.log (500000 / 988277) ∧
    -Real.log (500000 / 988277) ≤ (27254197 / 40000000) := by
  have h := checkLog_sound (w := (488277 / 1488277)) (n := 12)
    (lo := (170338731 / 250000000)) (hi := (27254197 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988277 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988277 / 500000) = 1/(500000 / 988277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (170338731 / 250000000) (27254197 / 40000000) (Real.log (988277 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (988277 / 500000) = -Real.log (500000 / 988277) := by
    rw [show ((988277 / 500000) : ℝ) = ((500000 / 988277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3753055371 / 1000000000) ≤ -Real.log (11723 / 500000) ∧
    -Real.log (11723 / 500000) ≤ (3753055377 / 1000000000) := by
  have h := checkLog_sound (w := (1951 / 13674)) (n := 12)
    (lo := (287319471 / 1000000000)) (hi := (17957467 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11723) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11723) = 1/(11723 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3753055377 / 1000000000) (-3753055371 / 1000000000) (Real.log (11723 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681431317 / 1000000000) ≤ -Real.log (200000 / 395341) ∧
    -Real.log (200000 / 395341) ≤ (340715659 / 500000000) := by
  have h := checkLog_sound (w := (195341 / 595341)) (n := 12)
    (lo := (681431317 / 1000000000)) (hi := (340715659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395341 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395341 / 200000) = 1/(200000 / 395341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681431317 / 1000000000) (340715659 / 500000000) (Real.log (395341 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (395341 / 200000) = -Real.log (200000 / 395341) := by
    rw [show ((395341 / 200000) : ℝ) = ((200000 / 395341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (375951653 / 100000000) ≤ -Real.log (4659 / 200000) ∧
    -Real.log (4659 / 200000) ≤ (469939567 / 125000000) := by
  have h := checkLog_sound (w := (1591 / 10909)) (n := 12)
    (lo := (29378063 / 100000000)) (hi := (293780631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4659) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 4659) = 1/(4659 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-469939567 / 125000000) (-375951653 / 100000000) (Real.log (4659 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2219974681 / 500000000) ≤ -Real.log (500000000000 / 42385324641907) ∧
    -Real.log (500000000000 / 42385324641907) ≤ (4439949369 / 1000000000) := by
  have h := checkLog_sound (w := (10385324641907 / 74385324641907)) (n := 12)
    (lo := (140533141 / 500000000)) (hi := (281066283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42385324641907 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(42385324641907 / 32000000000000) = 1/(500000000000 / 42385324641907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2219974681 / 500000000) (4439949369 / 1000000000) (Real.log (42385324641907 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (42385324641907 / 500000000000) = -Real.log (500000000000 / 42385324641907) := by
    rw [show ((42385324641907 / 500000000000) : ℝ) = ((500000000000 / 42385324641907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2223217577 / 500000000) ≤ -Real.log (15625000000 / 1333160014459) ∧
    -Real.log (15625000000 / 1333160014459) ≤ (4446435161 / 1000000000) := by
  have h := checkLog_sound (w := (333160014459 / 2333160014459)) (n := 12)
    (lo := (143776037 / 500000000)) (hi := (11502083 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333160014459 / 1000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1333160014459 / 1000000000000) = 1/(15625000000 / 1333160014459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2223217577 / 500000000) (4446435161 / 1000000000) (Real.log (1333160014459 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1333160014459 / 15625000000) = -Real.log (15625000000 / 1333160014459) := by
    rw [show ((1333160014459 / 15625000000) : ℝ) = ((15625000000 / 1333160014459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (886882059 / 200000000) ≤ -Real.log (500000000000 / 42151198498677) ∧
    -Real.log (500000000000 / 42151198498677) ≤ (2217205151 / 500000000) := by
  have h := checkLog_sound (w := (10151198498677 / 74151198498677)) (n := 12)
    (lo := (55105443 / 200000000)) (hi := (17220451 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42151198498677 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(42151198498677 / 32000000000000) = 1/(500000000000 / 42151198498677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (886882059 / 200000000) (2217205151 / 500000000) (Real.log (42151198498677 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (42151198498677 / 500000000000) = -Real.log (500000000000 / 42151198498677) := by
    rw [show ((42151198498677 / 500000000000) : ℝ) = ((500000000000 / 42151198498677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4440947847 / 1000000000) ≤ -Real.log (250000000000 / 21213833440653) ∧
    -Real.log (250000000000 / 21213833440653) ≤ (2220473927 / 500000000) := by
  have h := checkLog_sound (w := (5213833440653 / 37213833440653)) (n := 12)
    (lo := (282064767 / 1000000000)) (hi := (2203631 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21213833440653 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(21213833440653 / 16000000000000) = 1/(250000000000 / 21213833440653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4440947847 / 1000000000) (2220473927 / 500000000) (Real.log (21213833440653 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (21213833440653 / 250000000000) = -Real.log (250000000000 / 21213833440653) := by
    rw [show ((21213833440653 / 250000000000) : ℝ) = ((250000000000 / 21213833440653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0048
