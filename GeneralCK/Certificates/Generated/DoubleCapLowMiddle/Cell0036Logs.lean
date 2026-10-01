import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0036
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

theorem reflection_log_1_neg : (680375539 / 1000000000) ≤ -Real.log (102400 / 202201) ∧
    -Real.log (102400 / 202201) ≤ (34018777 / 50000000) := by
  have h := checkLog_sound (w := (99801 / 304601)) (n := 12)
    (lo := (680375539 / 1000000000)) (hi := (34018777 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202201 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202201 / 102400) = 1/(102400 / 202201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (680375539 / 1000000000) (34018777 / 50000000) (Real.log (202201 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202201 / 102400) = -Real.log (102400 / 202201) := by
    rw [show ((202201 / 102400) : ℝ) = ((102400 / 202201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1836879977 / 500000000) ≤ -Real.log (2599 / 102400) ∧
    -Real.log (2599 / 102400) ≤ (91843999 / 25000000) := by
  have h := checkLog_sound (w := (601 / 5799)) (n := 12)
    (lo := (104012027 / 500000000)) (hi := (41604811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2599) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2599) = 1/(2599 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-91843999 / 25000000) (-1836879977 / 500000000) (Real.log (2599 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (680281569 / 1000000000) ≤ -Real.log (51200 / 101091) ∧
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


theorem reflection_log_3 : Bounds (680281569 / 1000000000) (68028157 / 100000000) (Real.log (101091 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101091 / 51200) = -Real.log (51200 / 101091) := by
    rw [show ((101091 / 51200) : ℝ) = ((51200 / 101091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1833238021 / 500000000) ≤ -Real.log (1309 / 51200) ∧
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


theorem reflection_log_4 : Bounds (-229154753 / 62500000) (-1833238021 / 500000000) (Real.log (1309 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (667438671 / 1000000000) ≤ -Real.log (51200 / 99801) ∧
    -Real.log (51200 / 99801) ≤ (41714917 / 62500000) := by
  have h := checkLog_sound (w := (48601 / 151001)) (n := 12)
    (lo := (667438671 / 1000000000)) (hi := (41714917 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99801 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99801 / 51200) = 1/(51200 / 99801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (667438671 / 1000000000) (41714917 / 62500000) (Real.log (99801 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99801 / 51200) = -Real.log (51200 / 99801) := by
    rw [show ((99801 / 51200) : ℝ) = ((51200 / 99801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1490306387 / 500000000) ≤ -Real.log (2599 / 51200) ∧
    -Real.log (2599 / 51200) ≤ (2980612779 / 1000000000) := by
  have h := checkLog_sound (w := (601 / 5799)) (n := 12)
    (lo := (104012027 / 500000000)) (hi := (41604811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2599) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2599) = 1/(2599 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2980612779 / 1000000000) (-1490306387 / 500000000) (Real.log (2599 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (333624137 / 500000000) ≤ -Real.log (25600 / 49891) ∧
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


theorem reflection_log_7 : Bounds (333624137 / 500000000) (26689931 / 40000000) (Real.log (49891 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49891 / 25600) = -Real.log (25600 / 49891) := by
    rw [show ((49891 / 25600) : ℝ) = ((25600 / 49891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1486664431 / 500000000) ≤ -Real.log (1309 / 25600) ∧
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


theorem reflection_log_8 : Bounds (-2973328867 / 1000000000) (-1486664431 / 500000000) (Real.log (1309 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341161909 / 500000000) ≤ -Real.log (100000 / 197847) ∧
    -Real.log (100000 / 197847) ≤ (682323819 / 1000000000) := by
  have h := checkLog_sound (w := (97847 / 297847)) (n := 12)
    (lo := (341161909 / 500000000)) (hi := (682323819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197847 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197847 / 100000) = 1/(100000 / 197847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341161909 / 500000000) (682323819 / 1000000000) (Real.log (197847 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (197847 / 100000) = -Real.log (100000 / 197847) := by
    rw [show ((197847 / 100000) : ℝ) = ((100000 / 197847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (959576991 / 250000000) ≤ -Real.log (2153 / 100000) ∧
    -Real.log (2153 / 100000) ≤ (383830797 / 100000000) := by
  have h := checkLog_sound (w := (486 / 2639)) (n := 12)
    (lo := (11642877 / 31250000)) (hi := (74514413 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2153) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2153) = 1/(2153 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-383830797 / 100000000) (-959576991 / 250000000) (Real.log (2153 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42649977 / 62500000) ≤ -Real.log (50000 / 98931) ∧
    -Real.log (50000 / 98931) ≤ (682399633 / 1000000000) := by
  have h := checkLog_sound (w := (48931 / 148931)) (n := 12)
    (lo := (42649977 / 62500000)) (hi := (682399633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98931 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98931 / 50000) = 1/(50000 / 98931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42649977 / 62500000) (682399633 / 1000000000) (Real.log (98931 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (98931 / 50000) = -Real.log (50000 / 98931) := by
    rw [show ((98931 / 50000) : ℝ) = ((50000 / 98931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (384529937 / 100000000) ≤ -Real.log (1069 / 50000) ∧
    -Real.log (1069 / 50000) ≤ (240331211 / 62500000) := by
  have h := checkLog_sound (w := (987 / 5263)) (n := 12)
    (lo := (37956347 / 100000000)) (hi := (379563471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2138) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2138) = 1/(1069 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-240331211 / 62500000) (-384529937 / 100000000) (Real.log (1069 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (136453947 / 200000000) ≤ -Real.log (1000000 / 1978363) ∧
    -Real.log (1000000 / 1978363) ≤ (85283717 / 125000000) := by
  have h := checkLog_sound (w := (978363 / 2978363)) (n := 12)
    (lo := (136453947 / 200000000)) (hi := (85283717 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978363 / 1000000) = 1/(1000000 / 1978363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (136453947 / 200000000) (85283717 / 125000000) (Real.log (1978363 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1978363 / 1000000) = -Real.log (1000000 / 1978363) := by
    rw [show ((1978363 / 1000000) : ℝ) = ((1000000 / 1978363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3833350463 / 1000000000) ≤ -Real.log (21637 / 1000000) ∧
    -Real.log (21637 / 1000000) ≤ (3833350469 / 1000000000) := by
  have h := checkLog_sound (w := (9613 / 52887)) (n := 12)
    (lo := (367614563 / 1000000000)) (hi := (91903641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21637) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21637) = 1/(21637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3833350469 / 1000000000) (-3833350463 / 1000000000) (Real.log (21637 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (170586767 / 250000000) ≤ -Real.log (250000 / 494629) ∧
    -Real.log (250000 / 494629) ≤ (682347069 / 1000000000) := by
  have h := checkLog_sound (w := (244629 / 744629)) (n := 12)
    (lo := (170586767 / 250000000)) (hi := (682347069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494629 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494629 / 250000) = 1/(250000 / 494629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (170586767 / 250000000) (682347069 / 1000000000) (Real.log (494629 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (494629 / 250000) = -Real.log (250000 / 494629) := by
    rw [show ((494629 / 250000) : ℝ) = ((250000 / 494629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (960111701 / 250000000) ≤ -Real.log (5371 / 250000) ∧
    -Real.log (5371 / 250000) ≤ (384044681 / 100000000) := by
  have h := checkLog_sound (w := (4883 / 26367)) (n := 12)
    (lo := (46838863 / 125000000)) (hi := (74942181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10742) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10742) = 1/(5371 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-384044681 / 100000000) (-960111701 / 250000000) (Real.log (5371 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2260315891 / 500000000) ≤ -Real.log (25000000000 / 2297340919647) ∧
    -Real.log (25000000000 / 2297340919647) ≤ (4520631789 / 1000000000) := by
  have h := checkLog_sound (w := (697340919647 / 3897340919647)) (n := 12)
    (lo := (180874351 / 500000000)) (hi := (361748703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2297340919647 / 1600000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2297340919647 / 1600000000000) = 1/(25000000000 / 2297340919647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2260315891 / 500000000) (4520631789 / 1000000000) (Real.log (2297340919647 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2297340919647 / 25000000000) = -Real.log (25000000000 / 2297340919647) := by
    rw [show ((2297340919647 / 25000000000) : ℝ) = ((25000000000 / 2297340919647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2263849501 / 500000000) ≤ -Real.log (100000000000 / 9254536950421) ∧
    -Real.log (100000000000 / 9254536950421) ≤ (4527699009 / 1000000000) := by
  have h := checkLog_sound (w := (2854536950421 / 15654536950421)) (n := 12)
    (lo := (184407961 / 500000000)) (hi := (368815923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9254536950421 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9254536950421 / 6400000000000) = 1/(100000000000 / 9254536950421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2263849501 / 500000000) (4527699009 / 1000000000) (Real.log (9254536950421 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9254536950421 / 100000000000) = -Real.log (100000000000 / 9254536950421) := by
    rw [show ((9254536950421 / 100000000000) : ℝ) = ((100000000000 / 9254536950421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2257810099 / 500000000) ≤ -Real.log (500000000000 / 45717128067661) ∧
    -Real.log (500000000000 / 45717128067661) ≤ (903124041 / 200000000) := by
  have h := checkLog_sound (w := (13717128067661 / 77717128067661)) (n := 12)
    (lo := (178368559 / 500000000)) (hi := (356737119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45717128067661 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45717128067661 / 32000000000000) = 1/(500000000000 / 45717128067661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2257810099 / 500000000) (903124041 / 200000000) (Real.log (45717128067661 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (45717128067661 / 500000000000) = -Real.log (500000000000 / 45717128067661) := by
    rw [show ((45717128067661 / 500000000000) : ℝ) = ((500000000000 / 45717128067661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (282674617 / 62500000) ≤ -Real.log (125000000000 / 11511566747347) ∧
    -Real.log (125000000000 / 11511566747347) ≤ (4522793879 / 1000000000) := by
  have h := checkLog_sound (w := (3511566747347 / 19511566747347)) (n := 12)
    (lo := (45488849 / 125000000)) (hi := (363910793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11511566747347 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11511566747347 / 8000000000000) = 1/(125000000000 / 11511566747347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (282674617 / 62500000) (4522793879 / 1000000000) (Real.log (11511566747347 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (11511566747347 / 125000000000) = -Real.log (125000000000 / 11511566747347) := by
    rw [show ((11511566747347 / 125000000000) : ℝ) = ((125000000000 / 11511566747347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0036
