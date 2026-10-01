import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell037
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (240799267 / 1000000000) ≤ -Real.log (2560 / 3257) ∧
    -Real.log (2560 / 3257) ≤ (60199817 / 250000000) := by
  have h := checkLog_sound (w := (697 / 5817)) (n := 12)
    (lo := (240799267 / 1000000000)) (hi := (60199817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3257 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3257 / 2560) = 1/(2560 / 3257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (240799267 / 1000000000) (60199817 / 250000000) (Real.log (3257 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3257 / 2560) = -Real.log (2560 / 3257) := by
    rw [show ((3257 / 2560) : ℝ) = ((2560 / 3257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (158909583 / 500000000) ≤ -Real.log (1863 / 2560) ∧
    -Real.log (1863 / 2560) ≤ (317819167 / 1000000000) := by
  have h := checkLog_sound (w := (697 / 4423)) (n := 12)
    (lo := (158909583 / 500000000)) (hi := (317819167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1863) = 1/(1863 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-317819167 / 1000000000) (-158909583 / 500000000) (Real.log (1863 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (48067723 / 200000000) ≤ -Real.log (5120 / 6511) ∧
    -Real.log (5120 / 6511) ≤ (30042327 / 125000000) := by
  have h := checkLog_sound (w := (1391 / 11631)) (n := 12)
    (lo := (48067723 / 200000000)) (hi := (30042327 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6511 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6511 / 5120) = 1/(5120 / 6511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (48067723 / 200000000) (30042327 / 125000000) (Real.log (6511 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6511 / 5120) = -Real.log (5120 / 6511) := by
    rw [show ((6511 / 5120) : ℝ) = ((5120 / 6511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (317014337 / 1000000000) ≤ -Real.log (3729 / 5120) ∧
    -Real.log (3729 / 5120) ≤ (158507169 / 500000000) := by
  have h := checkLog_sound (w := (1391 / 8849)) (n := 12)
    (lo := (317014337 / 1000000000)) (hi := (158507169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3729) = 1/(3729 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-158507169 / 500000000) (-317014337 / 1000000000) (Real.log (3729 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (176233059 / 1000000000) ≤ -Real.log (250000 / 298179) ∧
    -Real.log (250000 / 298179) ≤ (8811653 / 50000000) := by
  have h := checkLog_sound (w := (48179 / 548179)) (n := 12)
    (lo := (176233059 / 1000000000)) (hi := (8811653 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298179 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298179 / 250000) = 1/(250000 / 298179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (176233059 / 1000000000) (8811653 / 50000000) (Real.log (298179 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (298179 / 250000) = -Real.log (250000 / 298179) := by
    rw [show ((298179 / 250000) : ℝ) = ((250000 / 298179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (214079751 / 1000000000) ≤ -Real.log (201821 / 250000) ∧
    -Real.log (201821 / 250000) ≤ (26759969 / 125000000) := by
  have h := checkLog_sound (w := (48179 / 451821)) (n := 12)
    (lo := (214079751 / 1000000000)) (hi := (26759969 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 201821) = 1/(201821 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26759969 / 125000000) (-214079751 / 1000000000) (Real.log (201821 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (22073037 / 125000000) ≤ -Real.log (200000 / 238627) ∧
    -Real.log (200000 / 238627) ≤ (176584297 / 1000000000) := by
  have h := checkLog_sound (w := (38627 / 438627)) (n := 12)
    (lo := (22073037 / 125000000)) (hi := (176584297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238627 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(238627 / 200000) = 1/(200000 / 238627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (22073037 / 125000000) (176584297 / 1000000000) (Real.log (238627 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (238627 / 200000) = -Real.log (200000 / 238627) := by
    rw [show ((238627 / 200000) : ℝ) = ((200000 / 238627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (21459891 / 100000000) ≤ -Real.log (161373 / 200000) ∧
    -Real.log (161373 / 200000) ≤ (214598911 / 1000000000) := by
  have h := checkLog_sound (w := (38627 / 361373)) (n := 12)
    (lo := (21459891 / 100000000)) (hi := (214598911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 161373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 161373) = 1/(161373 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-214598911 / 1000000000) (-21459891 / 100000000) (Real.log (161373 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (32249533 / 250000000) ≤ -Real.log (125000 / 142211) ∧
    -Real.log (125000 / 142211) ≤ (128998133 / 1000000000) := by
  have h := checkLog_sound (w := (17211 / 267211)) (n := 12)
    (lo := (32249533 / 250000000)) (hi := (128998133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142211 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142211 / 125000) = 1/(125000 / 142211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (32249533 / 250000000) (128998133 / 1000000000) (Real.log (142211 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (142211 / 125000) = -Real.log (125000 / 142211) := by
    rw [show ((142211 / 125000) : ℝ) = ((125000 / 142211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (37034531 / 250000000) ≤ -Real.log (107789 / 125000) ∧
    -Real.log (107789 / 125000) ≤ (237021 / 1600000) := by
  have h := checkLog_sound (w := (17211 / 232789)) (n := 12)
    (lo := (37034531 / 250000000)) (hi := (237021 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 107789) = 1/(107789 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-237021 / 1600000) (-37034531 / 250000000) (Real.log (107789 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (129267063 / 1000000000) ≤ -Real.log (500000 / 568997) ∧
    -Real.log (500000 / 568997) ≤ (16158383 / 125000000) := by
  have h := checkLog_sound (w := (68997 / 1068997)) (n := 12)
    (lo := (129267063 / 1000000000)) (hi := (16158383 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((568997 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(568997 / 500000) = 1/(500000 / 568997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (129267063 / 1000000000) (16158383 / 125000000) (Real.log (568997 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (568997 / 500000) = -Real.log (500000 / 568997) := by
    rw [show ((568997 / 500000) : ℝ) = ((500000 / 568997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (148493047 / 1000000000) ≤ -Real.log (431003 / 500000) ∧
    -Real.log (431003 / 500000) ≤ (18561631 / 125000000) := by
  have h := checkLog_sound (w := (68997 / 931003)) (n := 12)
    (lo := (148493047 / 1000000000)) (hi := (18561631 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 431003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 431003) = 1/(431003 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-18561631 / 125000000) (-148493047 / 1000000000) (Real.log (431003 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (557352953 / 1000000000) ≤ -Real.log (250000000000 / 436511128989) ∧
    -Real.log (250000000000 / 436511128989) ≤ (278676477 / 500000000) := by
  have h := checkLog_sound (w := (186511128989 / 686511128989)) (n := 12)
    (lo := (557352953 / 1000000000)) (hi := (278676477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((436511128989 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(436511128989 / 250000000000) = 1/(250000000000 / 436511128989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (557352953 / 1000000000) (278676477 / 500000000) (Real.log (436511128989 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (436511128989 / 250000000000) = -Real.log (250000000000 / 436511128989) := by
    rw [show ((436511128989 / 250000000000) : ℝ) = ((250000000000 / 436511128989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (279309217 / 500000000) ≤ -Real.log (25000000000 / 43706387547) ∧
    -Real.log (25000000000 / 43706387547) ≤ (111723687 / 200000000) := by
  have h := checkLog_sound (w := (18706387547 / 68706387547)) (n := 12)
    (lo := (279309217 / 500000000)) (hi := (111723687 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43706387547 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43706387547 / 25000000000) = 1/(25000000000 / 43706387547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (279309217 / 500000000) (111723687 / 200000000) (Real.log (43706387547 / 25000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (43706387547 / 25000000000) = -Real.log (25000000000 / 43706387547) := by
    rw [show ((43706387547 / 25000000000) : ℝ) = ((25000000000 / 43706387547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (390312811 / 1000000000) ≤ -Real.log (500000000000 / 738721441277) ∧
    -Real.log (500000000000 / 738721441277) ≤ (97578203 / 250000000) := by
  have h := checkLog_sound (w := (238721441277 / 1238721441277)) (n := 12)
    (lo := (390312811 / 1000000000)) (hi := (97578203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738721441277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738721441277 / 500000000000) = 1/(500000000000 / 738721441277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (390312811 / 1000000000) (97578203 / 250000000) (Real.log (738721441277 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (738721441277 / 500000000000) = -Real.log (500000000000 / 738721441277) := by
    rw [show ((738721441277 / 500000000000) : ℝ) = ((500000000000 / 738721441277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (391183207 / 1000000000) ≤ -Real.log (250000000000 / 369682350827) ∧
    -Real.log (250000000000 / 369682350827) ≤ (48897901 / 125000000) := by
  have h := checkLog_sound (w := (119682350827 / 619682350827)) (n := 12)
    (lo := (391183207 / 1000000000)) (hi := (48897901 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369682350827 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369682350827 / 250000000000) = 1/(250000000000 / 369682350827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (391183207 / 1000000000) (48897901 / 125000000) (Real.log (369682350827 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (369682350827 / 250000000000) = -Real.log (250000000000 / 369682350827) := by
    rw [show ((369682350827 / 250000000000) : ℝ) = ((250000000000 / 369682350827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (277136257 / 1000000000) ≤ -Real.log (500000000000 / 659673064969) ∧
    -Real.log (500000000000 / 659673064969) ≤ (138568129 / 500000000) := by
  have h := checkLog_sound (w := (159673064969 / 1159673064969)) (n := 12)
    (lo := (277136257 / 1000000000)) (hi := (138568129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659673064969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659673064969 / 500000000000) = 1/(500000000000 / 659673064969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (277136257 / 1000000000) (138568129 / 500000000) (Real.log (659673064969 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (659673064969 / 500000000000) = -Real.log (500000000000 / 659673064969) := by
    rw [show ((659673064969 / 500000000000) : ℝ) = ((500000000000 / 659673064969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (277760111 / 1000000000) ≤ -Real.log (500000000000 / 660084732589) ∧
    -Real.log (500000000000 / 660084732589) ≤ (17360007 / 62500000) := by
  have h := checkLog_sound (w := (160084732589 / 1160084732589)) (n := 12)
    (lo := (277760111 / 1000000000)) (hi := (17360007 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660084732589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660084732589 / 500000000000) = 1/(500000000000 / 660084732589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (277760111 / 1000000000) (17360007 / 62500000) (Real.log (660084732589 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (660084732589 / 500000000000) = -Real.log (500000000000 / 660084732589) := by
    rw [show ((660084732589 / 500000000000) : ℝ) = ((500000000000 / 660084732589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (150203 / 7812500) ≤ -Real.log (245239413991 / 250000000000) ∧
    -Real.log (245239413991 / 250000000000) ≤ (3845197 / 200000000) := by
  have h := checkLog_sound (w := (4760586009 / 495239413991)) (n := 12)
    (lo := (150203 / 7812500)) (hi := (3845197 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245239413991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245239413991) = 1/(245239413991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-3845197 / 200000000) (-150203 / 7812500) (Real.log (245239413991 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (19139991 / 1000000000) ≤ -Real.log (15328781479 / 15625000000) ∧
    -Real.log (15328781479 / 15625000000) ≤ (2392499 / 125000000) := by
  have h := checkLog_sound (w := (296218521 / 30953781479)) (n := 12)
    (lo := (19139991 / 1000000000)) (hi := (2392499 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15328781479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15328781479) = 1/(15328781479 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2392499 / 125000000) (-19139991 / 1000000000) (Real.log (15328781479 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell037
