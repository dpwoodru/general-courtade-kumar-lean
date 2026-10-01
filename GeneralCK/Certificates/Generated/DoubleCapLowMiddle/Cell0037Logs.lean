import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0037
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

theorem reflection_log_1_neg : (680281569 / 1000000000) ≤ -Real.log (51200 / 101091) ∧
    -Real.log (51200 / 101091) ≤ (68028157 / 100000000) := by
  have h := checkLog_sound (w := (49891 / 152291)) (n := 12)
    (lo := (680281569 / 1000000000)) (hi := (68028157 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101091 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101091 / 51200) = 1/(51200 / 101091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (680281569 / 1000000000) (68028157 / 100000000) (Real.log (101091 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101091 / 51200) = -Real.log (51200 / 101091) := by
    rw [show ((101091 / 51200) : ℝ) = ((51200 / 101091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1833238021 / 500000000) ≤ -Real.log (1309 / 51200) ∧
    -Real.log (1309 / 51200) ≤ (229154753 / 62500000) := by
  have h := checkLog_sound (w := (291 / 2909)) (n := 12)
    (lo := (100370071 / 500000000)) (hi := (200740143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1309) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1309) = 1/(1309 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-229154753 / 62500000) (-1833238021 / 500000000) (Real.log (1309 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (68018759 / 100000000) ≤ -Real.log (102400 / 202163) ∧
    -Real.log (102400 / 202163) ≤ (680187591 / 1000000000) := by
  have h := checkLog_sound (w := (99763 / 304563)) (n := 12)
    (lo := (68018759 / 100000000)) (hi := (680187591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202163 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202163 / 102400) = 1/(102400 / 202163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (68018759 / 100000000) (680187591 / 1000000000) (Real.log (202163 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202163 / 102400) = -Real.log (102400 / 202163) := by
    rw [show ((202163 / 102400) : ℝ) = ((102400 / 202163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1829622401 / 500000000) ≤ -Real.log (2637 / 102400) ∧
    -Real.log (2637 / 102400) ≤ (457405601 / 125000000) := by
  have h := checkLog_sound (w := (563 / 5837)) (n := 12)
    (lo := (96754451 / 500000000)) (hi := (193508903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2637) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2637) = 1/(2637 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-457405601 / 125000000) (-1829622401 / 500000000) (Real.log (2637 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (333624137 / 500000000) ≤ -Real.log (25600 / 49891) ∧
    -Real.log (25600 / 49891) ≤ (26689931 / 40000000) := by
  have h := checkLog_sound (w := (24291 / 75491)) (n := 12)
    (lo := (333624137 / 500000000)) (hi := (26689931 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49891 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49891 / 25600) = 1/(25600 / 49891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (333624137 / 500000000) (26689931 / 40000000) (Real.log (49891 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49891 / 25600) = -Real.log (25600 / 49891) := by
    rw [show ((49891 / 25600) : ℝ) = ((25600 / 49891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1486664431 / 500000000) ≤ -Real.log (1309 / 25600) ∧
    -Real.log (1309 / 25600) ≤ (2973328867 / 1000000000) := by
  have h := checkLog_sound (w := (291 / 2909)) (n := 12)
    (lo := (100370071 / 500000000)) (hi := (200740143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1309) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1309) = 1/(1309 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2973328867 / 1000000000) (-1486664431 / 500000000) (Real.log (1309 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (667057841 / 1000000000) ≤ -Real.log (51200 / 99763) ∧
    -Real.log (51200 / 99763) ≤ (333528921 / 500000000) := by
  have h := checkLog_sound (w := (48563 / 150963)) (n := 12)
    (lo := (667057841 / 1000000000)) (hi := (333528921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99763 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99763 / 51200) = 1/(51200 / 99763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (667057841 / 1000000000) (333528921 / 500000000) (Real.log (99763 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99763 / 51200) = -Real.log (51200 / 99763) := by
    rw [show ((99763 / 51200) : ℝ) = ((51200 / 99763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1483048811 / 500000000) ≤ -Real.log (2637 / 51200) ∧
    -Real.log (2637 / 51200) ≤ (2966097627 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 5837)) (n := 12)
    (lo := (96754451 / 500000000)) (hi := (193508903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2637) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2637) = 1/(2637 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2966097627 / 1000000000) (-1483048811 / 500000000) (Real.log (2637 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (682247999 / 1000000000) ≤ -Real.log (12500 / 24729) ∧
    -Real.log (12500 / 24729) ≤ (85281 / 125000) := by
  have h := checkLog_sound (w := (12229 / 37229)) (n := 12)
    (lo := (682247999 / 1000000000)) (hi := (85281 / 125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24729 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24729 / 12500) = 1/(12500 / 24729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (682247999 / 1000000000) (85281 / 125000) (Real.log (24729 / 12500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (24729 / 12500) = -Real.log (12500 / 24729) := by
    rw [show ((24729 / 12500) : ℝ) = ((12500 / 24729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3831365099 / 1000000000) ≤ -Real.log (271 / 12500) ∧
    -Real.log (271 / 12500) ≤ (766273021 / 200000000) := by
  have h := checkLog_sound (w := (957 / 5293)) (n := 12)
    (lo := (365629199 / 1000000000)) (hi := (914073 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2168) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2168) = 1/(271 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-766273021 / 200000000) (-3831365099 / 1000000000) (Real.log (271 / 12500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170581081 / 250000000) ≤ -Real.log (1000000 / 1978471) ∧
    -Real.log (1000000 / 1978471) ≤ (27292973 / 40000000) := by
  have h := checkLog_sound (w := (978471 / 2978471)) (n := 12)
    (lo := (170581081 / 250000000)) (hi := (27292973 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978471 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978471 / 1000000) = 1/(1000000 / 1978471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170581081 / 250000000) (27292973 / 40000000) (Real.log (1978471 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1978471 / 1000000) = -Real.log (1000000 / 1978471) := by
    rw [show ((1978471 / 1000000) : ℝ) = ((1000000 / 1978471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (959588603 / 250000000) ≤ -Real.log (21529 / 1000000) ∧
    -Real.log (21529 / 1000000) ≤ (1919177209 / 500000000) := by
  have h := checkLog_sound (w := (9721 / 52779)) (n := 12)
    (lo := (23288657 / 62500000)) (hi := (372618513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21529) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21529) = 1/(21529 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1919177209 / 500000000) (-959588603 / 250000000) (Real.log (21529 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (341096703 / 500000000) ≤ -Real.log (250000 / 494553) ∧
    -Real.log (250000 / 494553) ≤ (682193407 / 1000000000) := by
  have h := checkLog_sound (w := (244553 / 744553)) (n := 12)
    (lo := (341096703 / 500000000)) (hi := (682193407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494553 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494553 / 250000) = 1/(250000 / 494553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (341096703 / 500000000) (682193407 / 1000000000) (Real.log (494553 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (494553 / 250000) = -Real.log (250000 / 494553) := by
    rw [show ((494553 / 250000) : ℝ) = ((250000 / 494553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (956598979 / 250000000) ≤ -Real.log (5447 / 250000) ∧
    -Real.log (5447 / 250000) ≤ (1913197961 / 500000000) := by
  have h := checkLog_sound (w := (4731 / 26519)) (n := 12)
    (lo := (22541251 / 62500000)) (hi := (360660017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10894) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10894) = 1/(5447 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1913197961 / 500000000) (-956598979 / 250000000) (Real.log (5447 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (4264189 / 6250000) ≤ -Real.log (250000 / 494591) ∧
    -Real.log (250000 / 494591) ≤ (682270241 / 1000000000) := by
  have h := checkLog_sound (w := (244591 / 744591)) (n := 12)
    (lo := (4264189 / 6250000)) (hi := (682270241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494591 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494591 / 250000) = 1/(250000 / 494591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (4264189 / 6250000) (682270241 / 1000000000) (Real.log (494591 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (494591 / 250000) = -Real.log (250000 / 494591) := by
    rw [show ((494591 / 250000) : ℝ) = ((250000 / 494591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1916698341 / 500000000) ≤ -Real.log (5409 / 250000) ∧
    -Real.log (5409 / 250000) ≤ (239587293 / 62500000) := by
  have h := checkLog_sound (w := (4807 / 26443)) (n := 12)
    (lo := (183830391 / 500000000)) (hi := (367660783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10818) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10818) = 1/(5409 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-239587293 / 62500000) (-1916698341 / 500000000) (Real.log (5409 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2256806549 / 500000000) ≤ -Real.log (125000000000 / 11406365313653) ∧
    -Real.log (125000000000 / 11406365313653) ≤ (902722621 / 200000000) := by
  have h := checkLog_sound (w := (3406365313653 / 19406365313653)) (n := 12)
    (lo := (177365009 / 500000000)) (hi := (354730019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11406365313653 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11406365313653 / 8000000000000) = 1/(125000000000 / 11406365313653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2256806549 / 500000000) (902722621 / 200000000) (Real.log (11406365313653 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11406365313653 / 125000000000) = -Real.log (125000000000 / 11406365313653) := by
    rw [show ((11406365313653 / 125000000000) : ℝ) = ((125000000000 / 11406365313653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (282542421 / 62500000) ≤ -Real.log (125000000000 / 11487243950021) ∧
    -Real.log (125000000000 / 11487243950021) ≤ (4520678743 / 1000000000) := by
  have h := checkLog_sound (w := (3487243950021 / 19487243950021)) (n := 12)
    (lo := (45224457 / 125000000)) (hi := (361795657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11487243950021 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11487243950021 / 8000000000000) = 1/(125000000000 / 11487243950021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (282542421 / 62500000) (4520678743 / 1000000000) (Real.log (11487243950021 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11487243950021 / 125000000000) = -Real.log (125000000000 / 11487243950021) := by
    rw [show ((11487243950021 / 125000000000) : ℝ) = ((125000000000 / 11487243950021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2254294661 / 500000000) ≤ -Real.log (500000000000 / 45396823939783) ∧
    -Real.log (500000000000 / 45396823939783) ≤ (4508589329 / 1000000000) := by
  have h := checkLog_sound (w := (13396823939783 / 77396823939783)) (n := 12)
    (lo := (174853121 / 500000000)) (hi := (349706243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45396823939783 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45396823939783 / 32000000000000) = 1/(500000000000 / 45396823939783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2254294661 / 500000000) (4508589329 / 1000000000) (Real.log (45396823939783 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (45396823939783 / 500000000000) = -Real.log (500000000000 / 45396823939783) := by
    rw [show ((45396823939783 / 500000000000) : ℝ) = ((500000000000 / 45396823939783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2257833461 / 500000000) ≤ -Real.log (100000000000 / 9143852837863) ∧
    -Real.log (100000000000 / 9143852837863) ≤ (4515666929 / 1000000000) := by
  have h := checkLog_sound (w := (2743852837863 / 15543852837863)) (n := 12)
    (lo := (178391921 / 500000000)) (hi := (356783843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9143852837863 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9143852837863 / 6400000000000) = 1/(100000000000 / 9143852837863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2257833461 / 500000000) (4515666929 / 1000000000) (Real.log (9143852837863 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (9143852837863 / 100000000000) = -Real.log (100000000000 / 9143852837863) := by
    rw [show ((9143852837863 / 100000000000) : ℝ) = ((100000000000 / 9143852837863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0037
