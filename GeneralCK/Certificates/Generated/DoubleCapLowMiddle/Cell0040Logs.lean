import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0040
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

theorem reflection_log_1_neg : (135999921 / 200000000) ≤ -Real.log (4096 / 8085) ∧
    -Real.log (4096 / 8085) ≤ (339999803 / 500000000) := by
  have h := checkLog_sound (w := (3989 / 12181)) (n := 12)
    (lo := (135999921 / 200000000)) (hi := (339999803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8085 / 4096) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8085 / 4096) = 1/(4096 / 8085) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (135999921 / 200000000) (339999803 / 500000000) (Real.log (8085 / 4096)) := by
  have h := reflection_log_1_neg
  have he : Real.log (8085 / 4096) = -Real.log (4096 / 8085) := by
    rw [show ((8085 / 4096) : ℝ) = ((4096 / 8085) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3644937329 / 1000000000) ≤ -Real.log (107 / 4096) ∧
    -Real.log (107 / 4096) ≤ (728987467 / 200000000) := by
  have h := checkLog_sound (w := (21 / 235)) (n := 12)
    (lo := (179201429 / 1000000000)) (hi := (17920143 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 107) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(128 / 107) = 1/(107 / 4096) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-728987467 / 200000000) (-3644937329 / 1000000000) (Real.log (107 / 4096)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (679905599 / 1000000000) ≤ -Real.log (51200 / 101053) ∧
    -Real.log (51200 / 101053) ≤ (424941 / 625000) := by
  have h := checkLog_sound (w := (49853 / 152253)) (n := 12)
    (lo := (679905599 / 1000000000)) (hi := (424941 / 625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101053 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101053 / 51200) = 1/(51200 / 101053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (679905599 / 1000000000) (424941 / 625000) (Real.log (101053 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101053 / 51200) = -Real.log (51200 / 101053) := by
    rw [show ((101053 / 51200) : ℝ) = ((51200 / 101053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3637859631 / 1000000000) ≤ -Real.log (1347 / 51200) ∧
    -Real.log (1347 / 51200) ≤ (3637859637 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 2947)) (n := 12)
    (lo := (172123731 / 1000000000)) (hi := (43030933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1347) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1347) = 1/(1347 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3637859637 / 1000000000) (-3637859631 / 1000000000) (Real.log (1347 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (133335373 / 200000000) ≤ -Real.log (2048 / 3989) ∧
    -Real.log (2048 / 3989) ≤ (333338433 / 500000000) := by
  have h := checkLog_sound (w := (1941 / 6037)) (n := 12)
    (lo := (133335373 / 200000000)) (hi := (333338433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3989 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3989 / 2048) = 1/(2048 / 3989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (133335373 / 200000000) (333338433 / 500000000) (Real.log (3989 / 2048)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3989 / 2048) = -Real.log (2048 / 3989) := by
    rw [show ((3989 / 2048) : ℝ) = ((2048 / 3989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2951790149 / 1000000000) ≤ -Real.log (107 / 2048) ∧
    -Real.log (107 / 2048) ≤ (1475895077 / 500000000) := by
  have h := checkLog_sound (w := (21 / 235)) (n := 12)
    (lo := (179201429 / 1000000000)) (hi := (17920143 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 107) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(128 / 107) = 1/(107 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1475895077 / 500000000) (-2951790149 / 1000000000) (Real.log (107 / 2048)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (666486323 / 1000000000) ≤ -Real.log (25600 / 49853) ∧
    -Real.log (25600 / 49853) ≤ (166621581 / 250000000) := by
  have h := checkLog_sound (w := (24253 / 75453)) (n := 12)
    (lo := (666486323 / 1000000000)) (hi := (166621581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49853 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49853 / 25600) = 1/(25600 / 49853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (666486323 / 1000000000) (166621581 / 250000000) (Real.log (49853 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49853 / 25600) = -Real.log (25600 / 49853) := by
    rw [show ((49853 / 25600) : ℝ) = ((25600 / 49853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2944712451 / 1000000000) ≤ -Real.log (1347 / 25600) ∧
    -Real.log (1347 / 25600) ≤ (368089057 / 125000000) := by
  have h := checkLog_sound (w := (253 / 2947)) (n := 12)
    (lo := (172123731 / 1000000000)) (hi := (43030933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1347) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1347) = 1/(1347 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-368089057 / 125000000) (-2944712451 / 1000000000) (Real.log (1347 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85252753 / 125000000) ≤ -Real.log (1000000 / 1977873) ∧
    -Real.log (1000000 / 1977873) ≤ (27280881 / 40000000) := by
  have h := checkLog_sound (w := (977873 / 2977873)) (n := 12)
    (lo := (85252753 / 125000000)) (hi := (27280881 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977873 / 1000000) = 1/(1000000 / 1977873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85252753 / 125000000) (27280881 / 40000000) (Real.log (1977873 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1977873 / 1000000) = -Real.log (1000000 / 1977873) := by
    rw [show ((1977873 / 1000000) : ℝ) = ((1000000 / 1977873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3810956693 / 1000000000) ≤ -Real.log (22127 / 1000000) ∧
    -Real.log (22127 / 1000000) ≤ (3810956699 / 1000000000) := by
  have h := checkLog_sound (w := (9123 / 53377)) (n := 12)
    (lo := (345220793 / 1000000000)) (hi := (172610397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22127) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22127) = 1/(22127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3810956699 / 1000000000) (-3810956693 / 1000000000) (Real.log (22127 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (682097861 / 1000000000) ≤ -Real.log (1000000 / 1978023) ∧
    -Real.log (1000000 / 1978023) ≤ (341048931 / 500000000) := by
  have h := checkLog_sound (w := (978023 / 2978023)) (n := 12)
    (lo := (682097861 / 1000000000)) (hi := (341048931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978023 / 1000000) = 1/(1000000 / 1978023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (682097861 / 1000000000) (341048931 / 500000000) (Real.log (1978023 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1978023 / 1000000) = -Real.log (1000000 / 1978023) := by
    rw [show ((1978023 / 1000000) : ℝ) = ((1000000 / 1978023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (477219853 / 125000000) ≤ -Real.log (21977 / 1000000) ∧
    -Real.log (21977 / 1000000) ≤ (381775883 / 100000000) := by
  have h := checkLog_sound (w := (9273 / 53227)) (n := 12)
    (lo := (88005731 / 250000000)) (hi := (14080917 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21977) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21977) = 1/(21977 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-381775883 / 100000000) (-477219853 / 125000000) (Real.log (21977 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (136392877 / 200000000) ≤ -Real.log (1000000 / 1977759) ∧
    -Real.log (1000000 / 1977759) ≤ (340982193 / 500000000) := by
  have h := checkLog_sound (w := (977759 / 2977759)) (n := 12)
    (lo := (136392877 / 200000000)) (hi := (340982193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977759 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977759 / 1000000) = 1/(1000000 / 1977759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (136392877 / 200000000) (340982193 / 500000000) (Real.log (1977759 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1977759 / 1000000) = -Real.log (1000000 / 1977759) := by
    rw [show ((1977759 / 1000000) : ℝ) = ((1000000 / 1977759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3805817843 / 1000000000) ≤ -Real.log (22241 / 1000000) ∧
    -Real.log (22241 / 1000000) ≤ (3805817849 / 1000000000) := by
  have h := checkLog_sound (w := (9009 / 53491)) (n := 12)
    (lo := (340081943 / 1000000000)) (hi := (42510243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22241) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22241) = 1/(22241 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3805817849 / 1000000000) (-3805817843 / 1000000000) (Real.log (22241 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (682041237 / 1000000000) ≤ -Real.log (1000000 / 1977911) ∧
    -Real.log (1000000 / 1977911) ≤ (341020619 / 500000000) := by
  have h := checkLog_sound (w := (977911 / 2977911)) (n := 12)
    (lo := (682041237 / 1000000000)) (hi := (341020619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977911 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977911 / 1000000) = 1/(1000000 / 1977911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (682041237 / 1000000000) (341020619 / 500000000) (Real.log (1977911 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1977911 / 1000000) = -Real.log (1000000 / 1977911) := by
    rw [show ((1977911 / 1000000) : ℝ) = ((1000000 / 1977911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3812675529 / 1000000000) ≤ -Real.log (22089 / 1000000) ∧
    -Real.log (22089 / 1000000) ≤ (762535107 / 200000000) := by
  have h := checkLog_sound (w := (9161 / 53339)) (n := 12)
    (lo := (346939629 / 1000000000)) (hi := (34693963 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22089) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22089) = 1/(22089 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-762535107 / 200000000) (-3812675529 / 1000000000) (Real.log (22089 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2246489359 / 500000000) ≤ -Real.log (31250000000 / 2793353425679) ∧
    -Real.log (31250000000 / 2793353425679) ≤ (179719149 / 40000000) := by
  have h := checkLog_sound (w := (793353425679 / 4793353425679)) (n := 12)
    (lo := (167047819 / 500000000)) (hi := (334095639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2793353425679 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2793353425679 / 2000000000000) = 1/(31250000000 / 2793353425679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2246489359 / 500000000) (179719149 / 40000000) (Real.log (2793353425679 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2793353425679 / 31250000000) = -Real.log (31250000000 / 2793353425679) := by
    rw [show ((2793353425679 / 31250000000) : ℝ) = ((31250000000 / 2793353425679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1124964171 / 250000000) ≤ -Real.log (500000000000 / 45002115848387) ∧
    -Real.log (500000000000 / 45002115848387) ≤ (4499856691 / 1000000000) := by
  have h := checkLog_sound (w := (13002115848387 / 77002115848387)) (n := 12)
    (lo := (85243401 / 250000000)) (hi := (68194721 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45002115848387 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(45002115848387 / 32000000000000) = 1/(500000000000 / 45002115848387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1124964171 / 250000000) (4499856691 / 1000000000) (Real.log (45002115848387 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (45002115848387 / 500000000000) = -Real.log (500000000000 / 45002115848387) := by
    rw [show ((45002115848387 / 500000000000) : ℝ) = ((500000000000 / 45002115848387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1121945557 / 250000000) ≤ -Real.log (500000000000 / 44462007103997) ∧
    -Real.log (500000000000 / 44462007103997) ≤ (897556447 / 200000000) := by
  have h := checkLog_sound (w := (12462007103997 / 76462007103997)) (n := 12)
    (lo := (82224787 / 250000000)) (hi := (328899149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44462007103997 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(44462007103997 / 32000000000000) = 1/(500000000000 / 44462007103997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1121945557 / 250000000) (897556447 / 200000000) (Real.log (44462007103997 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (44462007103997 / 500000000000) = -Real.log (500000000000 / 44462007103997) := by
    rw [show ((44462007103997 / 500000000000) : ℝ) = ((500000000000 / 44462007103997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (898943353 / 200000000) ≤ -Real.log (250000000000 / 22385701027661) ∧
    -Real.log (250000000000 / 22385701027661) ≤ (1123679193 / 250000000) := by
  have h := checkLog_sound (w := (6385701027661 / 38385701027661)) (n := 12)
    (lo := (67166737 / 200000000)) (hi := (167916843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22385701027661 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(22385701027661 / 16000000000000) = 1/(250000000000 / 22385701027661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (898943353 / 200000000) (1123679193 / 250000000) (Real.log (22385701027661 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (22385701027661 / 250000000000) = -Real.log (250000000000 / 22385701027661) := by
    rw [show ((22385701027661 / 250000000000) : ℝ) = ((250000000000 / 22385701027661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0040
