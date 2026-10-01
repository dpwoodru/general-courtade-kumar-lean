import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0041
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

theorem reflection_log_1_neg : (679905599 / 1000000000) ≤ -Real.log (51200 / 101053) ∧
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


theorem reflection_log_1 : Bounds (679905599 / 1000000000) (424941 / 625000) (Real.log (101053 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101053 / 51200) = -Real.log (51200 / 101053) := by
    rw [show ((101053 / 51200) : ℝ) = ((51200 / 101053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3637859631 / 1000000000) ≤ -Real.log (1347 / 51200) ∧
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


theorem reflection_log_2 : Bounds (-3637859637 / 1000000000) (-3637859631 / 1000000000) (Real.log (1347 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (135962317 / 200000000) ≤ -Real.log (102400 / 202087) ∧
    -Real.log (102400 / 202087) ≤ (339905793 / 500000000) := by
  have h := checkLog_sound (w := (99687 / 304487)) (n := 12)
    (lo := (135962317 / 200000000)) (hi := (339905793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202087 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202087 / 102400) = 1/(102400 / 202087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (135962317 / 200000000) (339905793 / 500000000) (Real.log (202087 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202087 / 102400) = -Real.log (102400 / 202087) := by
    rw [show ((202087 / 102400) : ℝ) = ((102400 / 202087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (907707919 / 250000000) ≤ -Real.log (2713 / 102400) ∧
    -Real.log (2713 / 102400) ≤ (1815415841 / 500000000) := by
  have h := checkLog_sound (w := (487 / 5913)) (n := 12)
    (lo := (5159243 / 31250000)) (hi := (165095777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2713) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2713) = 1/(2713 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1815415841 / 500000000) (-907707919 / 250000000) (Real.log (2713 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (666486323 / 1000000000) ≤ -Real.log (25600 / 49853) ∧
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


theorem reflection_log_5 : Bounds (666486323 / 1000000000) (166621581 / 250000000) (Real.log (49853 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49853 / 25600) = -Real.log (25600 / 49853) := by
    rw [show ((49853 / 25600) : ℝ) = ((25600 / 49853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2944712451 / 1000000000) ≤ -Real.log (1347 / 25600) ∧
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


theorem reflection_log_6 : Bounds (-368089057 / 125000000) (-2944712451 / 1000000000) (Real.log (1347 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (133259149 / 200000000) ≤ -Real.log (51200 / 99687) ∧
    -Real.log (51200 / 99687) ≤ (333147873 / 500000000) := by
  have h := checkLog_sound (w := (48487 / 150887)) (n := 12)
    (lo := (133259149 / 200000000)) (hi := (333147873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99687 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99687 / 51200) = 1/(51200 / 99687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (133259149 / 200000000) (333147873 / 500000000) (Real.log (99687 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99687 / 51200) = -Real.log (51200 / 99687) := by
    rw [show ((99687 / 51200) : ℝ) = ((51200 / 99687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (183605281 / 62500000) ≤ -Real.log (2713 / 51200) ∧
    -Real.log (2713 / 51200) ≤ (2937684501 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 5913)) (n := 12)
    (lo := (5159243 / 31250000)) (hi := (165095777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2713) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2713) = 1/(2713 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2937684501 / 1000000000) (-183605281 / 62500000) (Real.log (2713 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340973091 / 500000000) ≤ -Real.log (1000000 / 1977723) ∧
    -Real.log (1000000 / 1977723) ≤ (681946183 / 1000000000) := by
  have h := checkLog_sound (w := (977723 / 2977723)) (n := 12)
    (lo := (340973091 / 500000000)) (hi := (681946183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977723 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977723 / 1000000) = 1/(1000000 / 1977723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340973091 / 500000000) (681946183 / 1000000000) (Real.log (1977723 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1977723 / 1000000) = -Real.log (1000000 / 1977723) := by
    rw [show ((1977723 / 1000000) : ℝ) = ((1000000 / 1977723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (95105013 / 25000000) ≤ -Real.log (22277 / 1000000) ∧
    -Real.log (22277 / 1000000) ≤ (1902100263 / 500000000) := by
  have h := checkLog_sound (w := (8973 / 53527)) (n := 12)
    (lo := (16923231 / 50000000)) (hi := (338464621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22277) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22277) = 1/(22277 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1902100263 / 500000000) (-95105013 / 25000000) (Real.log (22277 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (68202253 / 100000000) ≤ -Real.log (500000 / 988937) ∧
    -Real.log (500000 / 988937) ≤ (682022531 / 1000000000) := by
  have h := checkLog_sound (w := (488937 / 1488937)) (n := 12)
    (lo := (68202253 / 100000000)) (hi := (682022531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988937 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988937 / 500000) = 1/(500000 / 988937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (68202253 / 100000000) (682022531 / 1000000000) (Real.log (988937 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (988937 / 500000) = -Real.log (500000 / 988937) := by
    rw [show ((988937 / 500000) : ℝ) = ((500000 / 988937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (119093809 / 31250000) ≤ -Real.log (11063 / 500000) ∧
    -Real.log (11063 / 500000) ≤ (1905500947 / 500000000) := by
  have h := checkLog_sound (w := (2281 / 13344)) (n := 12)
    (lo := (86316497 / 250000000)) (hi := (345265989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11063) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11063) = 1/(11063 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1905500947 / 500000000) (-119093809 / 31250000) (Real.log (11063 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681888033 / 1000000000) ≤ -Real.log (125000 / 247201) ∧
    -Real.log (125000 / 247201) ≤ (340944017 / 500000000) := by
  have h := checkLog_sound (w := (122201 / 372201)) (n := 12)
    (lo := (681888033 / 1000000000)) (hi := (340944017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247201 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247201 / 125000) = 1/(125000 / 247201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681888033 / 1000000000) (340944017 / 500000000) (Real.log (247201 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (247201 / 125000) = -Real.log (125000 / 247201) := by
    rw [show ((247201 / 125000) : ℝ) = ((125000 / 247201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3799051523 / 1000000000) ≤ -Real.log (2799 / 125000) ∧
    -Real.log (2799 / 125000) ≤ (3799051529 / 1000000000) := by
  have h := checkLog_sound (w := (4429 / 26821)) (n := 12)
    (lo := (333315623 / 1000000000)) (hi := (41664453 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11196) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11196) = 1/(2799 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3799051529 / 1000000000) (-3799051523 / 1000000000) (Real.log (2799 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681964891 / 1000000000) ≤ -Real.log (6250 / 12361) ∧
    -Real.log (6250 / 12361) ≤ (170491223 / 250000000) := by
  have h := checkLog_sound (w := (6111 / 18611)) (n := 12)
    (lo := (681964891 / 1000000000)) (hi := (170491223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12361 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12361 / 6250) = 1/(6250 / 12361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681964891 / 1000000000) (170491223 / 250000000) (Real.log (12361 / 6250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (12361 / 6250) = -Real.log (6250 / 12361) := by
    rw [show ((12361 / 6250) : ℝ) = ((6250 / 12361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1902931403 / 500000000) ≤ -Real.log (139 / 6250) ∧
    -Real.log (139 / 6250) ≤ (951465703 / 250000000) := by
  have h := checkLog_sound (w := (901 / 5349)) (n := 12)
    (lo := (170063453 / 500000000)) (hi := (340126907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2224) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2224) = 1/(139 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-951465703 / 250000000) (-1902931403 / 500000000) (Real.log (139 / 6250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2243073351 / 500000000) ≤ -Real.log (500000000000 / 44389347757777) ∧
    -Real.log (500000000000 / 44389347757777) ≤ (4486146709 / 1000000000) := by
  have h := checkLog_sound (w := (12389347757777 / 76389347757777)) (n := 12)
    (lo := (163631811 / 500000000)) (hi := (327263623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44389347757777 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(44389347757777 / 32000000000000) = 1/(500000000000 / 44389347757777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2243073351 / 500000000) (4486146709 / 1000000000) (Real.log (44389347757777 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (44389347757777 / 500000000000) = -Real.log (500000000000 / 44389347757777) := by
    rw [show ((44389347757777 / 500000000000) : ℝ) = ((500000000000 / 44389347757777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2246512209 / 500000000) ≤ -Real.log (500000000000 / 44695697369611) ∧
    -Real.log (500000000000 / 44695697369611) ≤ (179720977 / 40000000) := by
  have h := checkLog_sound (w := (12695697369611 / 76695697369611)) (n := 12)
    (lo := (167070669 / 500000000)) (hi := (334141339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44695697369611 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(44695697369611 / 32000000000000) = 1/(500000000000 / 44695697369611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2246512209 / 500000000) (179720977 / 40000000) (Real.log (44695697369611 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (44695697369611 / 500000000000) = -Real.log (500000000000 / 44695697369611) := by
    rw [show ((44695697369611 / 500000000000) : ℝ) = ((500000000000 / 44695697369611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1120234889 / 250000000) ≤ -Real.log (125000000000 / 11039701679171) ∧
    -Real.log (125000000000 / 11039701679171) ≤ (4480939563 / 1000000000) := by
  have h := checkLog_sound (w := (3039701679171 / 19039701679171)) (n := 12)
    (lo := (80514119 / 250000000)) (hi := (322056477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11039701679171 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11039701679171 / 8000000000000) = 1/(125000000000 / 11039701679171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1120234889 / 250000000) (4480939563 / 1000000000) (Real.log (11039701679171 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11039701679171 / 125000000000) = -Real.log (125000000000 / 11039701679171) := by
    rw [show ((11039701679171 / 125000000000) : ℝ) = ((125000000000 / 11039701679171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4487827697 / 1000000000) ≤ -Real.log (500000000000 / 44464028776979) ∧
    -Real.log (500000000000 / 44464028776979) ≤ (560978463 / 125000000) := by
  have h := checkLog_sound (w := (12464028776979 / 76464028776979)) (n := 12)
    (lo := (328944617 / 1000000000)) (hi := (164472309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44464028776979 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(44464028776979 / 32000000000000) = 1/(500000000000 / 44464028776979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4487827697 / 1000000000) (560978463 / 125000000) (Real.log (44464028776979 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (44464028776979 / 500000000000) = -Real.log (500000000000 / 44464028776979) := by
    rw [show ((44464028776979 / 500000000000) : ℝ) = ((500000000000 / 44464028776979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0041
