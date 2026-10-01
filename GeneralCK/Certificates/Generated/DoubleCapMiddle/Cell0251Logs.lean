import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0251
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

theorem reflection_log_1_neg : (121243257 / 500000000) ≤ -Real.log (1024 / 1305) ∧
    -Real.log (1024 / 1305) ≤ (48497303 / 200000000) := by
  have h := checkLog_sound (w := (281 / 2329)) (n := 12)
    (lo := (121243257 / 500000000)) (hi := (48497303 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1305 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1305 / 1024) = 1/(1024 / 1305) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (121243257 / 500000000) (48497303 / 200000000) (Real.log (1305 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1305 / 1024) = -Real.log (1024 / 1305) := by
    rw [show ((1305 / 1024) : ℝ) = ((1024 / 1305) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (4009697 / 12500000) ≤ -Real.log (743 / 1024) ∧
    -Real.log (743 / 1024) ≤ (320775761 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 1767)) (n := 12)
    (lo := (4009697 / 12500000)) (hi := (320775761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 743) = 1/(743 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-320775761 / 1000000000) (-4009697 / 12500000) (Real.log (743 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (121013319 / 500000000) ≤ -Real.log (2560 / 3261) ∧
    -Real.log (2560 / 3261) ≤ (242026639 / 1000000000) := by
  have h := checkLog_sound (w := (701 / 5821)) (n := 12)
    (lo := (121013319 / 500000000)) (hi := (242026639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3261 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3261 / 2560) = 1/(2560 / 3261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (121013319 / 500000000) (242026639 / 1000000000) (Real.log (3261 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3261 / 2560) = -Real.log (2560 / 3261) := by
    rw [show ((3261 / 2560) : ℝ) = ((2560 / 3261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (319968549 / 1000000000) ≤ -Real.log (1859 / 2560) ∧
    -Real.log (1859 / 2560) ≤ (6399371 / 20000000) := by
  have h := checkLog_sound (w := (701 / 4419)) (n := 12)
    (lo := (319968549 / 1000000000)) (hi := (6399371 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1859) = 1/(1859 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6399371 / 20000000) (-319968549 / 1000000000) (Real.log (1859 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (109374649 / 250000000) ≤ -Real.log (512 / 793) ∧
    -Real.log (512 / 793) ≤ (437498597 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 1305)) (n := 12)
    (lo := (109374649 / 250000000)) (hi := (437498597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(793 / 512) = 1/(512 / 793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (109374649 / 250000000) (437498597 / 1000000000) (Real.log (793 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (793 / 512) = -Real.log (512 / 793) := by
    rw [show ((793 / 512) : ℝ) = ((512 / 793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (795906913 / 1000000000) ≤ -Real.log (231 / 512) ∧
    -Real.log (231 / 512) ≤ (159181383 / 200000000) := by
  have h := checkLog_sound (w := (25 / 487)) (n := 12)
    (lo := (102759733 / 1000000000)) (hi := (51379867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 231) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 231) = 1/(231 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-159181383 / 200000000) (-795906913 / 1000000000) (Real.log (231 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (436741689 / 1000000000) ≤ -Real.log (1280 / 1981) ∧
    -Real.log (1280 / 1981) ≤ (43674169 / 100000000) := by
  have h := checkLog_sound (w := (701 / 3261)) (n := 12)
    (lo := (436741689 / 1000000000)) (hi := (43674169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981 / 1280) = 1/(1280 / 1981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (436741689 / 1000000000) (43674169 / 100000000) (Real.log (1981 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1981 / 1280) = -Real.log (1280 / 1981) := by
    rw [show ((1981 / 1280) : ℝ) = ((1280 / 1981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (396656439 / 500000000) ≤ -Real.log (579 / 1280) ∧
    -Real.log (579 / 1280) ≤ (9916411 / 12500000) := by
  have h := checkLog_sound (w := (61 / 1219)) (n := 12)
    (lo := (50082849 / 500000000)) (hi := (100165699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 579) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 579) = 1/(579 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9916411 / 12500000) (-396656439 / 500000000) (Real.log (579 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (331325443 / 1000000000) ≤ -Real.log (1000000 / 1392813) ∧
    -Real.log (1000000 / 1392813) ≤ (82831361 / 250000000) := by
  have h := checkLog_sound (w := (392813 / 2392813)) (n := 12)
    (lo := (331325443 / 1000000000)) (hi := (82831361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1392813 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1392813 / 1000000) = 1/(1000000 / 1392813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (331325443 / 1000000000) (82831361 / 250000000) (Real.log (1392813 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1392813 / 1000000) = -Real.log (1000000 / 1392813) := by
    rw [show ((1392813 / 1000000) : ℝ) = ((1000000 / 1392813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (249459231 / 500000000) ≤ -Real.log (607187 / 1000000) ∧
    -Real.log (607187 / 1000000) ≤ (498918463 / 1000000000) := by
  have h := checkLog_sound (w := (392813 / 1607187)) (n := 12)
    (lo := (249459231 / 500000000)) (hi := (498918463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 607187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 607187) = 1/(607187 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-498918463 / 1000000000) (-249459231 / 500000000) (Real.log (607187 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (66389833 / 200000000) ≤ -Real.log (500000 / 696841) ∧
    -Real.log (500000 / 696841) ≤ (165974583 / 500000000) := by
  have h := checkLog_sound (w := (196841 / 1196841)) (n := 12)
    (lo := (66389833 / 200000000)) (hi := (165974583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696841 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696841 / 500000) = 1/(500000 / 696841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (66389833 / 200000000) (165974583 / 500000000) (Real.log (696841 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (696841 / 500000) = -Real.log (500000 / 696841) := by
    rw [show ((696841 / 500000) : ℝ) = ((500000 / 696841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (250175339 / 500000000) ≤ -Real.log (303159 / 500000) ∧
    -Real.log (303159 / 500000) ≤ (500350679 / 1000000000) := by
  have h := checkLog_sound (w := (196841 / 803159)) (n := 12)
    (lo := (250175339 / 500000000)) (hi := (500350679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 303159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 303159) = 1/(303159 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-500350679 / 1000000000) (-250175339 / 500000000) (Real.log (303159 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (63687491 / 250000000) ≤ -Real.log (1000000 / 1290139) ∧
    -Real.log (1000000 / 1290139) ≤ (50949993 / 200000000) := by
  have h := checkLog_sound (w := (290139 / 2290139)) (n := 12)
    (lo := (63687491 / 250000000)) (hi := (50949993 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1290139 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1290139 / 1000000) = 1/(1000000 / 1290139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (63687491 / 250000000) (50949993 / 200000000) (Real.log (1290139 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1290139 / 1000000) = -Real.log (1000000 / 1290139) := by
    rw [show ((1290139 / 1000000) : ℝ) = ((1000000 / 1290139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (171343051 / 500000000) ≤ -Real.log (709861 / 1000000) ∧
    -Real.log (709861 / 1000000) ≤ (342686103 / 1000000000) := by
  have h := checkLog_sound (w := (290139 / 1709861)) (n := 12)
    (lo := (171343051 / 500000000)) (hi := (342686103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 709861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 709861) = 1/(709861 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-342686103 / 1000000000) (-171343051 / 500000000) (Real.log (709861 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (255291619 / 1000000000) ≤ -Real.log (500000 / 645419) ∧
    -Real.log (500000 / 645419) ≤ (12764581 / 50000000) := by
  have h := checkLog_sound (w := (145419 / 1145419)) (n := 12)
    (lo := (255291619 / 1000000000)) (hi := (12764581 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((645419 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(645419 / 500000) = 1/(500000 / 645419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (255291619 / 1000000000) (12764581 / 50000000) (Real.log (645419 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (645419 / 500000) = -Real.log (500000 / 645419) := by
    rw [show ((645419 / 500000) : ℝ) = ((500000 / 645419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (343671287 / 1000000000) ≤ -Real.log (354581 / 500000) ∧
    -Real.log (354581 / 500000) ≤ (42958911 / 125000000) := by
  have h := checkLog_sound (w := (145419 / 854581)) (n := 12)
    (lo := (343671287 / 1000000000)) (hi := (42958911 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 354581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 354581) = 1/(354581 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-42958911 / 125000000) (-343671287 / 1000000000) (Real.log (354581 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (166048781 / 200000000) ≤ -Real.log (50000000000 / 114693908137) ∧
    -Real.log (50000000000 / 114693908137) ≤ (830243907 / 1000000000) := by
  have h := checkLog_sound (w := (14693908137 / 214693908137)) (n := 12)
    (lo := (5483869 / 40000000)) (hi := (68548363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114693908137 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(114693908137 / 100000000000) = 1/(50000000000 / 114693908137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (166048781 / 200000000) (830243907 / 1000000000) (Real.log (114693908137 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (114693908137 / 50000000000) = -Real.log (50000000000 / 114693908137) := by
    rw [show ((114693908137 / 50000000000) : ℝ) = ((50000000000 / 114693908137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (832299843 / 1000000000) ≤ -Real.log (100000000000 / 229859908497) ∧
    -Real.log (100000000000 / 229859908497) ≤ (166459969 / 200000000) := by
  have h := checkLog_sound (w := (29859908497 / 429859908497)) (n := 12)
    (lo := (139152663 / 1000000000)) (hi := (17394083 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229859908497 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(229859908497 / 200000000000) = 1/(100000000000 / 229859908497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (832299843 / 1000000000) (166459969 / 200000000) (Real.log (229859908497 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (229859908497 / 100000000000) = -Real.log (100000000000 / 229859908497) := by
    rw [show ((229859908497 / 100000000000) : ℝ) = ((100000000000 / 229859908497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (597436067 / 1000000000) ≤ -Real.log (500000000000 / 908726497159) ∧
    -Real.log (500000000000 / 908726497159) ≤ (149359017 / 250000000) := by
  have h := checkLog_sound (w := (408726497159 / 1408726497159)) (n := 12)
    (lo := (597436067 / 1000000000)) (hi := (149359017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((908726497159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(908726497159 / 500000000000) = 1/(500000000000 / 908726497159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (597436067 / 1000000000) (149359017 / 250000000) (Real.log (908726497159 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (908726497159 / 500000000000) = -Real.log (500000000000 / 908726497159) := by
    rw [show ((908726497159 / 500000000000) : ℝ) = ((500000000000 / 908726497159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (598962907 / 1000000000) ≤ -Real.log (100000000000 / 182023007437) ∧
    -Real.log (100000000000 / 182023007437) ≤ (149740727 / 250000000) := by
  have h := checkLog_sound (w := (82023007437 / 282023007437)) (n := 12)
    (lo := (598962907 / 1000000000)) (hi := (149740727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182023007437 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182023007437 / 100000000000) = 1/(100000000000 / 182023007437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (598962907 / 1000000000) (149740727 / 250000000) (Real.log (182023007437 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (182023007437 / 100000000000) = -Real.log (100000000000 / 182023007437) := by
    rw [show ((182023007437 / 100000000000) : ℝ) = ((100000000000 / 182023007437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0251
