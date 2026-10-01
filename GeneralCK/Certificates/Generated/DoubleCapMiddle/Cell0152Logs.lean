import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0152
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

theorem reflection_log_1_neg : (144377857 / 500000000) ≤ -Real.log (2560 / 3417) ∧
    -Real.log (2560 / 3417) ≤ (57751143 / 200000000) := by
  have h := checkLog_sound (w := (857 / 5977)) (n := 12)
    (lo := (144377857 / 500000000)) (hi := (57751143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3417 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3417 / 2560) = 1/(2560 / 3417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (144377857 / 500000000) (57751143 / 200000000) (Real.log (3417 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3417 / 2560) = -Real.log (2560 / 3417) := by
    rw [show ((3417 / 2560) : ℝ) = ((2560 / 3417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (25475991 / 62500000) ≤ -Real.log (1703 / 2560) ∧
    -Real.log (1703 / 2560) ≤ (407615857 / 1000000000) := by
  have h := checkLog_sound (w := (857 / 4263)) (n := 12)
    (lo := (25475991 / 62500000)) (hi := (407615857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1703) = 1/(1703 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-407615857 / 1000000000) (-25475991 / 62500000) (Real.log (1703 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (57575473 / 200000000) ≤ -Real.log (1280 / 1707) ∧
    -Real.log (1280 / 1707) ≤ (143938683 / 500000000) := by
  have h := checkLog_sound (w := (427 / 2987)) (n := 12)
    (lo := (57575473 / 200000000)) (hi := (143938683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1707 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1707 / 1280) = 1/(1280 / 1707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (57575473 / 200000000) (143938683 / 500000000) (Real.log (1707 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1707 / 1280) = -Real.log (1280 / 1707) := by
    rw [show ((1707 / 1280) : ℝ) = ((1280 / 1707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (405855809 / 1000000000) ≤ -Real.log (853 / 1280) ∧
    -Real.log (853 / 1280) ≤ (40585581 / 100000000) := by
  have h := checkLog_sound (w := (427 / 2133)) (n := 12)
    (lo := (405855809 / 1000000000)) (hi := (40585581 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 853) = 1/(853 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-40585581 / 100000000) (-405855809 / 1000000000) (Real.log (853 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (256271449 / 500000000) ≤ -Real.log (1280 / 2137) ∧
    -Real.log (1280 / 2137) ≤ (512542899 / 1000000000) := by
  have h := checkLog_sound (w := (857 / 3417)) (n := 12)
    (lo := (256271449 / 500000000)) (hi := (512542899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2137 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2137 / 1280) = 1/(1280 / 2137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (256271449 / 500000000) (512542899 / 1000000000) (Real.log (2137 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2137 / 1280) = -Real.log (1280 / 2137) := by
    rw [show ((2137 / 1280) : ℝ) = ((1280 / 2137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1107243177 / 1000000000) ≤ -Real.log (423 / 1280) ∧
    -Real.log (423 / 1280) ≤ (1107243179 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1063)) (n := 12)
    (lo := (414095997 / 1000000000)) (hi := (207047999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 423) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 423) = 1/(423 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1107243179 / 1000000000) (-1107243177 / 1000000000) (Real.log (423 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (255569037 / 500000000) ≤ -Real.log (640 / 1067) ∧
    -Real.log (640 / 1067) ≤ (20445523 / 40000000) := by
  have h := checkLog_sound (w := (427 / 1707)) (n := 12)
    (lo := (255569037 / 500000000)) (hi := (20445523 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1067 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1067 / 640) = 1/(640 / 1067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (255569037 / 500000000) (20445523 / 40000000) (Real.log (1067 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1067 / 640) = -Real.log (640 / 1067) := by
    rw [show ((1067 / 640) : ℝ) = ((640 / 1067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (110017601 / 100000000) ≤ -Real.log (213 / 640) ∧
    -Real.log (213 / 640) ≤ (275044003 / 250000000) := by
  have h := checkLog_sound (w := (107 / 533)) (n := 12)
    (lo := (40702883 / 100000000)) (hi := (407028831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 213) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 213) = 1/(213 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-275044003 / 250000000) (-110017601 / 100000000) (Real.log (213 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (9846467 / 25000000) ≤ -Real.log (1000000 / 1482691) ∧
    -Real.log (1000000 / 1482691) ≤ (393858681 / 1000000000) := by
  have h := checkLog_sound (w := (482691 / 2482691)) (n := 12)
    (lo := (9846467 / 25000000)) (hi := (393858681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1482691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1482691 / 1000000) = 1/(1000000 / 1482691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (9846467 / 25000000) (393858681 / 1000000000) (Real.log (1482691 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1482691 / 1000000) = -Real.log (1000000 / 1482691) := by
    rw [show ((1482691 / 1000000) : ℝ) = ((1000000 / 1482691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (82389363 / 125000000) ≤ -Real.log (517309 / 1000000) ∧
    -Real.log (517309 / 1000000) ≤ (131822981 / 200000000) := by
  have h := checkLog_sound (w := (482691 / 1517309)) (n := 12)
    (lo := (82389363 / 125000000)) (hi := (131822981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 517309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 517309) = 1/(517309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-131822981 / 200000000) (-82389363 / 125000000) (Real.log (517309 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (49383573 / 125000000) ≤ -Real.log (500000 / 742243) ∧
    -Real.log (500000 / 742243) ≤ (79013717 / 200000000) := by
  have h := checkLog_sound (w := (242243 / 1242243)) (n := 12)
    (lo := (49383573 / 125000000)) (hi := (79013717 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742243 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742243 / 500000) = 1/(500000 / 742243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (49383573 / 125000000) (79013717 / 200000000) (Real.log (742243 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (742243 / 500000) = -Real.log (500000 / 742243) := by
    rw [show ((742243 / 500000) : ℝ) = ((500000 / 742243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (662590817 / 1000000000) ≤ -Real.log (257757 / 500000) ∧
    -Real.log (257757 / 500000) ≤ (331295409 / 500000000) := by
  have h := checkLog_sound (w := (242243 / 757757)) (n := 12)
    (lo := (662590817 / 1000000000)) (hi := (331295409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 257757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 257757) = 1/(257757 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-331295409 / 500000000) (-662590817 / 1000000000) (Real.log (257757 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (77745563 / 250000000) ≤ -Real.log (200000 / 272953) ∧
    -Real.log (200000 / 272953) ≤ (310982253 / 1000000000) := by
  have h := checkLog_sound (w := (72953 / 472953)) (n := 12)
    (lo := (77745563 / 250000000)) (hi := (310982253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272953 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272953 / 200000) = 1/(200000 / 272953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (77745563 / 250000000) (310982253 / 1000000000) (Real.log (272953 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (272953 / 200000) = -Real.log (200000 / 272953) := by
    rw [show ((272953 / 200000) : ℝ) = ((200000 / 272953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (453760269 / 1000000000) ≤ -Real.log (127047 / 200000) ∧
    -Real.log (127047 / 200000) ≤ (45376027 / 100000000) := by
  have h := checkLog_sound (w := (72953 / 327047)) (n := 12)
    (lo := (453760269 / 1000000000)) (hi := (45376027 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 127047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 127047) = 1/(127047 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-45376027 / 100000000) (-453760269 / 1000000000) (Real.log (127047 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (312112211 / 1000000000) ≤ -Real.log (250000 / 341577) ∧
    -Real.log (250000 / 341577) ≤ (78028053 / 250000000) := by
  have h := checkLog_sound (w := (91577 / 591577)) (n := 12)
    (lo := (312112211 / 1000000000)) (hi := (78028053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341577 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341577 / 250000) = 1/(250000 / 341577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (312112211 / 1000000000) (78028053 / 250000000) (Real.log (341577 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (341577 / 250000) = -Real.log (250000 / 341577) := by
    rw [show ((341577 / 250000) : ℝ) = ((250000 / 341577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (456192247 / 1000000000) ≤ -Real.log (158423 / 250000) ∧
    -Real.log (158423 / 250000) ≤ (57024031 / 125000000) := by
  have h := checkLog_sound (w := (91577 / 408423)) (n := 12)
    (lo := (456192247 / 1000000000)) (hi := (57024031 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 158423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 158423) = 1/(158423 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-57024031 / 125000000) (-456192247 / 1000000000) (Real.log (158423 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1052973583 / 1000000000) ≤ -Real.log (25000000000 / 71654030763) ∧
    -Real.log (25000000000 / 71654030763) ≤ (210594717 / 200000000) := by
  have h := checkLog_sound (w := (21654030763 / 121654030763)) (n := 12)
    (lo := (359826403 / 1000000000)) (hi := (89956601 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71654030763 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(71654030763 / 50000000000) = 1/(25000000000 / 71654030763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1052973583 / 1000000000) (210594717 / 200000000) (Real.log (71654030763 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (71654030763 / 25000000000) = -Real.log (25000000000 / 71654030763) := by
    rw [show ((71654030763 / 25000000000) : ℝ) = ((25000000000 / 71654030763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1057659401 / 1000000000) ≤ -Real.log (62500000000 / 179976440989) ∧
    -Real.log (62500000000 / 179976440989) ≤ (1057659403 / 1000000000) := by
  have h := checkLog_sound (w := (54976440989 / 304976440989)) (n := 12)
    (lo := (364512221 / 1000000000)) (hi := (182256111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179976440989 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(179976440989 / 125000000000) = 1/(62500000000 / 179976440989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1057659401 / 1000000000) (1057659403 / 1000000000) (Real.log (179976440989 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (179976440989 / 62500000000) = -Real.log (62500000000 / 179976440989) := by
    rw [show ((179976440989 / 62500000000) : ℝ) = ((62500000000 / 179976440989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (764742521 / 1000000000) ≤ -Real.log (500000000000 / 1074220564043) ∧
    -Real.log (500000000000 / 1074220564043) ≤ (764742523 / 1000000000) := by
  have h := checkLog_sound (w := (74220564043 / 2074220564043)) (n := 12)
    (lo := (71595341 / 1000000000)) (hi := (35797671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1074220564043 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1074220564043 / 1000000000000) = 1/(500000000000 / 1074220564043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (764742521 / 1000000000) (764742523 / 1000000000) (Real.log (1074220564043 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1074220564043 / 500000000000) = -Real.log (500000000000 / 1074220564043) := by
    rw [show ((1074220564043 / 500000000000) : ℝ) = ((500000000000 / 1074220564043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (384152229 / 500000000) ≤ -Real.log (500000000000 / 1078053691699) ∧
    -Real.log (500000000000 / 1078053691699) ≤ (38415223 / 50000000) := by
  have h := checkLog_sound (w := (78053691699 / 2078053691699)) (n := 12)
    (lo := (37578639 / 500000000)) (hi := (75157279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078053691699 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1078053691699 / 1000000000000) = 1/(500000000000 / 1078053691699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (384152229 / 500000000) (38415223 / 50000000) (Real.log (1078053691699 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1078053691699 / 500000000000) = -Real.log (500000000000 / 1078053691699) := by
    rw [show ((1078053691699 / 500000000000) : ℝ) = ((500000000000 / 1078053691699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0152
