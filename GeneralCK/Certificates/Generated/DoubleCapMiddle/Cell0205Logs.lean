import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0205
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

theorem reflection_log_1_neg : (131707697 / 500000000) ≤ -Real.log (5120 / 6663) ∧
    -Real.log (5120 / 6663) ≤ (52683079 / 200000000) := by
  have h := checkLog_sound (w := (1543 / 11783)) (n := 12)
    (lo := (131707697 / 500000000)) (hi := (52683079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6663 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6663 / 5120) = 1/(5120 / 6663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (131707697 / 500000000) (52683079 / 200000000) (Real.log (6663 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6663 / 5120) = -Real.log (5120 / 6663) := by
    rw [show ((6663 / 5120) : ℝ) = ((5120 / 6663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (179314989 / 500000000) ≤ -Real.log (3577 / 5120) ∧
    -Real.log (3577 / 5120) ≤ (358629979 / 1000000000) := by
  have h := checkLog_sound (w := (1543 / 8697)) (n := 12)
    (lo := (179314989 / 500000000)) (hi := (358629979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3577) = 1/(3577 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-358629979 / 1000000000) (-179314989 / 500000000) (Real.log (3577 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (52593009 / 200000000) ≤ -Real.log (256 / 333) ∧
    -Real.log (256 / 333) ≤ (131482523 / 500000000) := by
  have h := checkLog_sound (w := (77 / 589)) (n := 12)
    (lo := (52593009 / 200000000)) (hi := (131482523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333 / 256) = 1/(256 / 333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (52593009 / 200000000) (131482523 / 500000000) (Real.log (333 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (333 / 256) = -Real.log (256 / 333) := by
    rw [show ((333 / 256) : ℝ) = ((256 / 333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (178895819 / 500000000) ≤ -Real.log (179 / 256) ∧
    -Real.log (179 / 256) ≤ (357791639 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 435)) (n := 12)
    (lo := (178895819 / 500000000)) (hi := (357791639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 179) = 1/(179 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-357791639 / 1000000000) (-178895819 / 500000000) (Real.log (179 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (235855577 / 500000000) ≤ -Real.log (2560 / 4103) ∧
    -Real.log (2560 / 4103) ≤ (94342231 / 200000000) := by
  have h := checkLog_sound (w := (1543 / 6663)) (n := 12)
    (lo := (235855577 / 500000000)) (hi := (94342231 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4103 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4103 / 2560) = 1/(2560 / 4103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (235855577 / 500000000) (94342231 / 200000000) (Real.log (4103 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4103 / 2560) = -Real.log (2560 / 4103) := by
    rw [show ((4103 / 2560) : ℝ) = ((2560 / 4103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (46157507 / 50000000) ≤ -Real.log (1017 / 2560) ∧
    -Real.log (1017 / 2560) ≤ (461575071 / 500000000) := by
  have h := checkLog_sound (w := (263 / 2297)) (n := 12)
    (lo := (2875037 / 12500000)) (hi := (230002961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1017) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1017) = 1/(1017 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-461575071 / 500000000) (-46157507 / 50000000) (Real.log (1017 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (94195943 / 200000000) ≤ -Real.log (128 / 205) ∧
    -Real.log (128 / 205) ≤ (117744929 / 250000000) := by
  have h := checkLog_sound (w := (77 / 333)) (n := 12)
    (lo := (94195943 / 200000000)) (hi := (117744929 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205 / 128) = 1/(128 / 205) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (94195943 / 200000000) (117744929 / 250000000) (Real.log (205 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (205 / 128) = -Real.log (128 / 205) := by
    rw [show ((205 / 128) : ℝ) = ((128 / 205) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (92020463 / 100000000) ≤ -Real.log (51 / 128) ∧
    -Real.log (51 / 128) ≤ (115025579 / 125000000) := by
  have h := checkLog_sound (w := (13 / 115)) (n := 12)
    (lo := (4541149 / 20000000)) (hi := (227057451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 51) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 51) = 1/(51 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-115025579 / 125000000) (-92020463 / 100000000) (Real.log (51 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (179882283 / 500000000) ≤ -Real.log (31250 / 44781) ∧
    -Real.log (31250 / 44781) ≤ (359764567 / 1000000000) := by
  have h := checkLog_sound (w := (13531 / 76031)) (n := 12)
    (lo := (179882283 / 500000000)) (hi := (359764567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44781 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44781 / 31250) = 1/(31250 / 44781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (179882283 / 500000000) (359764567 / 1000000000) (Real.log (44781 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (44781 / 31250) = -Real.log (31250 / 44781) := by
    rw [show ((44781 / 31250) : ℝ) = ((31250 / 44781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (283690933 / 500000000) ≤ -Real.log (17719 / 31250) ∧
    -Real.log (17719 / 31250) ≤ (567381867 / 1000000000) := by
  have h := checkLog_sound (w := (13531 / 48969)) (n := 12)
    (lo := (283690933 / 500000000)) (hi := (567381867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 17719) = 1/(17719 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-567381867 / 1000000000) (-283690933 / 500000000) (Real.log (17719 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (360378477 / 1000000000) ≤ -Real.log (62500 / 89617) ∧
    -Real.log (62500 / 89617) ≤ (180189239 / 500000000) := by
  have h := checkLog_sound (w := (27117 / 152117)) (n := 12)
    (lo := (360378477 / 1000000000)) (hi := (180189239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89617 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89617 / 62500) = 1/(62500 / 89617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (360378477 / 1000000000) (180189239 / 500000000) (Real.log (89617 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (89617 / 62500) = -Real.log (62500 / 89617) := by
    rw [show ((89617 / 62500) : ℝ) = ((62500 / 89617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (568935077 / 1000000000) ≤ -Real.log (35383 / 62500) ∧
    -Real.log (35383 / 62500) ≤ (284467539 / 500000000) := by
  have h := checkLog_sound (w := (27117 / 97883)) (n := 12)
    (lo := (568935077 / 1000000000)) (hi := (284467539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 35383) = 1/(35383 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-284467539 / 500000000) (-568935077 / 1000000000) (Real.log (35383 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (34977909 / 125000000) ≤ -Real.log (62500 / 82681) ∧
    -Real.log (62500 / 82681) ≤ (279823273 / 1000000000) := by
  have h := checkLog_sound (w := (20181 / 145181)) (n := 12)
    (lo := (34977909 / 125000000)) (hi := (279823273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82681 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82681 / 62500) = 1/(62500 / 82681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (34977909 / 125000000) (279823273 / 1000000000) (Real.log (82681 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (82681 / 62500) = -Real.log (62500 / 82681) := by
    rw [show ((82681 / 62500) : ℝ) = ((62500 / 82681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (194965199 / 500000000) ≤ -Real.log (42319 / 62500) ∧
    -Real.log (42319 / 62500) ≤ (389930399 / 1000000000) := by
  have h := checkLog_sound (w := (20181 / 104819)) (n := 12)
    (lo := (194965199 / 500000000)) (hi := (389930399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 42319) = 1/(42319 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-389930399 / 1000000000) (-194965199 / 500000000) (Real.log (42319 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (280373429 / 1000000000) ≤ -Real.log (125000 / 165453) ∧
    -Real.log (125000 / 165453) ≤ (28037343 / 100000000) := by
  have h := checkLog_sound (w := (40453 / 290453)) (n := 12)
    (lo := (280373429 / 1000000000)) (hi := (28037343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165453 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165453 / 125000) = 1/(125000 / 165453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (280373429 / 1000000000) (28037343 / 100000000) (Real.log (165453 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (165453 / 125000) = -Real.log (125000 / 165453) := by
    rw [show ((165453 / 125000) : ℝ) = ((125000 / 165453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (6109471 / 15625000) ≤ -Real.log (84547 / 125000) ∧
    -Real.log (84547 / 125000) ≤ (78201229 / 200000000) := by
  have h := checkLog_sound (w := (40453 / 209547)) (n := 12)
    (lo := (6109471 / 15625000)) (hi := (78201229 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 84547) = 1/(84547 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-78201229 / 200000000) (-6109471 / 15625000) (Real.log (84547 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (927146431 / 1000000000) ≤ -Real.log (20000000000 / 50545741859) ∧
    -Real.log (20000000000 / 50545741859) ≤ (927146433 / 1000000000) := by
  have h := checkLog_sound (w := (10545741859 / 90545741859)) (n := 12)
    (lo := (233999251 / 1000000000)) (hi := (58499813 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50545741859 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50545741859 / 40000000000) = 1/(20000000000 / 50545741859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (927146431 / 1000000000) (927146433 / 1000000000) (Real.log (50545741859 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (50545741859 / 20000000000) = -Real.log (20000000000 / 50545741859) := by
    rw [show ((50545741859 / 20000000000) : ℝ) = ((20000000000 / 50545741859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (464656777 / 500000000) ≤ -Real.log (500000000000 / 1266384987141) ∧
    -Real.log (500000000000 / 1266384987141) ≤ (232328389 / 250000000) := by
  have h := checkLog_sound (w := (266384987141 / 2266384987141)) (n := 12)
    (lo := (118083187 / 500000000)) (hi := (1889331 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1266384987141 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1266384987141 / 1000000000000) = 1/(500000000000 / 1266384987141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (464656777 / 500000000) (232328389 / 250000000) (Real.log (1266384987141 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1266384987141 / 500000000000) = -Real.log (500000000000 / 1266384987141) := by
    rw [show ((1266384987141 / 500000000000) : ℝ) = ((500000000000 / 1266384987141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (669753671 / 1000000000) ≤ -Real.log (250000000000 / 488438999031) ∧
    -Real.log (250000000000 / 488438999031) ≤ (83719209 / 125000000) := by
  have h := checkLog_sound (w := (238438999031 / 738438999031)) (n := 12)
    (lo := (669753671 / 1000000000)) (hi := (83719209 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((488438999031 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(488438999031 / 250000000000) = 1/(250000000000 / 488438999031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (669753671 / 1000000000) (83719209 / 125000000) (Real.log (488438999031 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (488438999031 / 250000000000) = -Real.log (250000000000 / 488438999031) := by
    rw [show ((488438999031 / 250000000000) : ℝ) = ((250000000000 / 488438999031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (671379573 / 1000000000) ≤ -Real.log (100000000000 / 195693519581) ∧
    -Real.log (100000000000 / 195693519581) ≤ (335689787 / 500000000) := by
  have h := checkLog_sound (w := (95693519581 / 295693519581)) (n := 12)
    (lo := (671379573 / 1000000000)) (hi := (335689787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195693519581 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195693519581 / 100000000000) = 1/(100000000000 / 195693519581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (671379573 / 1000000000) (335689787 / 500000000) (Real.log (195693519581 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (195693519581 / 100000000000) = -Real.log (100000000000 / 195693519581) := by
    rw [show ((195693519581 / 100000000000) : ℝ) = ((100000000000 / 195693519581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0205
