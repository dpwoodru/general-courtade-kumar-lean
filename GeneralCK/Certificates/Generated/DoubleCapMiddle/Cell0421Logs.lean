import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0421
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

theorem reflection_log_1_neg : (19517801 / 100000000) ≤ -Real.log (10240 / 12447) ∧
    -Real.log (10240 / 12447) ≤ (195178011 / 1000000000) := by
  have h := checkLog_sound (w := (2207 / 22687)) (n := 12)
    (lo := (19517801 / 100000000)) (hi := (195178011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12447 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12447 / 10240) = 1/(10240 / 12447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (19517801 / 100000000) (195178011 / 1000000000) (Real.log (12447 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12447 / 10240) = -Real.log (10240 / 12447) := by
    rw [show ((12447 / 10240) : ℝ) = ((10240 / 12447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (121371781 / 500000000) ≤ -Real.log (8033 / 10240) ∧
    -Real.log (8033 / 10240) ≤ (242743563 / 1000000000) := by
  have h := checkLog_sound (w := (2207 / 18273)) (n := 12)
    (lo := (121371781 / 500000000)) (hi := (242743563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8033) = 1/(8033 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-242743563 / 1000000000) (-121371781 / 500000000) (Real.log (8033 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (194936959 / 1000000000) ≤ -Real.log (2560 / 3111) ∧
    -Real.log (2560 / 3111) ≤ (304589 / 1562500) := by
  have h := checkLog_sound (w := (551 / 5671)) (n := 12)
    (lo := (194936959 / 1000000000)) (hi := (304589 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3111 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3111 / 2560) = 1/(2560 / 3111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (194936959 / 1000000000) (304589 / 1562500) (Real.log (3111 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3111 / 2560) = -Real.log (2560 / 3111) := by
    rw [show ((3111 / 2560) : ℝ) = ((2560 / 3111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (60592543 / 250000000) ≤ -Real.log (2009 / 2560) ∧
    -Real.log (2009 / 2560) ≤ (242370173 / 1000000000) := by
  have h := checkLog_sound (w := (551 / 4569)) (n := 12)
    (lo := (60592543 / 250000000)) (hi := (242370173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 2009) = 1/(2009 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-242370173 / 1000000000) (-60592543 / 250000000) (Real.log (2009 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (89602929 / 250000000) ≤ -Real.log (5120 / 7327) ∧
    -Real.log (5120 / 7327) ≤ (358411717 / 1000000000) := by
  have h := checkLog_sound (w := (2207 / 12447)) (n := 12)
    (lo := (89602929 / 250000000)) (hi := (358411717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7327 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7327 / 5120) = 1/(5120 / 7327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (89602929 / 250000000) (358411717 / 1000000000) (Real.log (7327 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7327 / 5120) = -Real.log (5120 / 7327) := by
    rw [show ((7327 / 5120) : ℝ) = ((5120 / 7327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (563970961 / 1000000000) ≤ -Real.log (2913 / 5120) ∧
    -Real.log (2913 / 5120) ≤ (281985481 / 500000000) := by
  have h := checkLog_sound (w := (2207 / 8033)) (n := 12)
    (lo := (563970961 / 1000000000)) (hi := (281985481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2913) = 1/(2913 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-281985481 / 500000000) (-563970961 / 1000000000) (Real.log (2913 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (358002187 / 1000000000) ≤ -Real.log (1280 / 1831) ∧
    -Real.log (1280 / 1831) ≤ (89500547 / 250000000) := by
  have h := checkLog_sound (w := (551 / 3111)) (n := 12)
    (lo := (358002187 / 1000000000)) (hi := (89500547 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1831 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1831 / 1280) = 1/(1280 / 1831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (358002187 / 1000000000) (89500547 / 250000000) (Real.log (1831 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1831 / 1280) = -Real.log (1280 / 1831) := by
    rw [show ((1831 / 1280) : ℝ) = ((1280 / 1831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (70367703 / 125000000) ≤ -Real.log (729 / 1280) ∧
    -Real.log (729 / 1280) ≤ (4503533 / 8000000) := by
  have h := checkLog_sound (w := (551 / 2009)) (n := 12)
    (lo := (70367703 / 125000000)) (hi := (4503533 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 729) = 1/(729 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-4503533 / 8000000) (-70367703 / 125000000) (Real.log (729 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (66921749 / 250000000) ≤ -Real.log (500000 / 653469) ∧
    -Real.log (500000 / 653469) ≤ (267686997 / 1000000000) := by
  have h := checkLog_sound (w := (153469 / 1153469)) (n := 12)
    (lo := (66921749 / 250000000)) (hi := (267686997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((653469 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(653469 / 500000) = 1/(500000 / 653469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (66921749 / 250000000) (267686997 / 1000000000) (Real.log (653469 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (653469 / 500000) = -Real.log (500000 / 653469) := by
    rw [show ((653469 / 500000) : ℝ) = ((500000 / 653469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (366635817 / 1000000000) ≤ -Real.log (346531 / 500000) ∧
    -Real.log (346531 / 500000) ≤ (183317909 / 500000000) := by
  have h := checkLog_sound (w := (153469 / 846531)) (n := 12)
    (lo := (366635817 / 1000000000)) (hi := (183317909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 346531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 346531) = 1/(346531 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-183317909 / 500000000) (-366635817 / 1000000000) (Real.log (346531 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (8375403 / 31250000) ≤ -Real.log (250000 / 326841) ∧
    -Real.log (250000 / 326841) ≤ (268012897 / 1000000000) := by
  have h := checkLog_sound (w := (76841 / 576841)) (n := 12)
    (lo := (8375403 / 31250000)) (hi := (268012897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326841 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326841 / 250000) = 1/(250000 / 326841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (8375403 / 31250000) (268012897 / 1000000000) (Real.log (326841 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (326841 / 250000) = -Real.log (250000 / 326841) := by
    rw [show ((326841 / 250000) : ℝ) = ((250000 / 326841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (36725067 / 100000000) ≤ -Real.log (173159 / 250000) ∧
    -Real.log (173159 / 250000) ≤ (367250671 / 1000000000) := by
  have h := checkLog_sound (w := (76841 / 423159)) (n := 12)
    (lo := (36725067 / 100000000)) (hi := (367250671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 173159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 173159) = 1/(173159 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-367250671 / 1000000000) (-36725067 / 100000000) (Real.log (173159 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (201184199 / 1000000000) ≤ -Real.log (20000 / 24457) ∧
    -Real.log (20000 / 24457) ≤ (1005921 / 5000000) := by
  have h := checkLog_sound (w := (4457 / 44457)) (n := 12)
    (lo := (201184199 / 1000000000)) (hi := (1005921 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24457 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24457 / 20000) = 1/(20000 / 24457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (201184199 / 1000000000) (1005921 / 5000000) (Real.log (24457 / 20000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (24457 / 20000) = -Real.log (20000 / 24457) := by
    rw [show ((24457 / 20000) : ℝ) = ((20000 / 24457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (252121897 / 1000000000) ≤ -Real.log (15543 / 20000) ∧
    -Real.log (15543 / 20000) ≤ (126060949 / 500000000) := by
  have h := checkLog_sound (w := (4457 / 35543)) (n := 12)
    (lo := (252121897 / 1000000000)) (hi := (126060949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15543) = 1/(15543 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-126060949 / 500000000) (-252121897 / 1000000000) (Real.log (15543 / 20000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (50362893 / 250000000) ≤ -Real.log (1000000 / 1223177) ∧
    -Real.log (1000000 / 1223177) ≤ (201451573 / 1000000000) := by
  have h := checkLog_sound (w := (223177 / 2223177)) (n := 12)
    (lo := (50362893 / 250000000)) (hi := (201451573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223177 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223177 / 1000000) = 1/(1000000 / 1223177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (50362893 / 250000000) (201451573 / 1000000000) (Real.log (1223177 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1223177 / 1000000) = -Real.log (1000000 / 1223177) := by
    rw [show ((1223177 / 1000000) : ℝ) = ((1000000 / 1223177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (252542753 / 1000000000) ≤ -Real.log (776823 / 1000000) ∧
    -Real.log (776823 / 1000000) ≤ (126271377 / 500000000) := by
  have h := checkLog_sound (w := (223177 / 1776823)) (n := 12)
    (lo := (252542753 / 1000000000)) (hi := (126271377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 776823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 776823) = 1/(776823 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-126271377 / 500000000) (-252542753 / 1000000000) (Real.log (776823 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (317161407 / 500000000) ≤ -Real.log (250000000000 / 471436177427) ∧
    -Real.log (250000000000 / 471436177427) ≤ (126864563 / 200000000) := by
  have h := checkLog_sound (w := (221436177427 / 721436177427)) (n := 12)
    (lo := (317161407 / 500000000)) (hi := (126864563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471436177427 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471436177427 / 250000000000) = 1/(250000000000 / 471436177427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (317161407 / 500000000) (126864563 / 200000000) (Real.log (471436177427 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (471436177427 / 250000000000) = -Real.log (250000000000 / 471436177427) := by
    rw [show ((471436177427 / 250000000000) : ℝ) = ((250000000000 / 471436177427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (317631783 / 500000000) ≤ -Real.log (500000000000 / 943759781473) ∧
    -Real.log (500000000000 / 943759781473) ≤ (635263567 / 1000000000) := by
  have h := checkLog_sound (w := (443759781473 / 1443759781473)) (n := 12)
    (lo := (317631783 / 500000000)) (hi := (635263567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((943759781473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(943759781473 / 500000000000) = 1/(500000000000 / 943759781473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (317631783 / 500000000) (635263567 / 1000000000) (Real.log (943759781473 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (943759781473 / 500000000000) = -Real.log (500000000000 / 943759781473) := by
    rw [show ((943759781473 / 500000000000) : ℝ) = ((500000000000 / 943759781473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (453306097 / 1000000000) ≤ -Real.log (500000000000 / 786752879109) ∧
    -Real.log (500000000000 / 786752879109) ≤ (226653049 / 500000000) := by
  have h := checkLog_sound (w := (286752879109 / 1286752879109)) (n := 12)
    (lo := (453306097 / 1000000000)) (hi := (226653049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((786752879109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(786752879109 / 500000000000) = 1/(500000000000 / 786752879109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (453306097 / 1000000000) (226653049 / 500000000) (Real.log (786752879109 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (786752879109 / 500000000000) = -Real.log (500000000000 / 786752879109) := by
    rw [show ((786752879109 / 500000000000) : ℝ) = ((500000000000 / 786752879109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (226997163 / 500000000) ≤ -Real.log (250000000000 / 393647265851) ∧
    -Real.log (250000000000 / 393647265851) ≤ (453994327 / 1000000000) := by
  have h := checkLog_sound (w := (143647265851 / 643647265851)) (n := 12)
    (lo := (226997163 / 500000000)) (hi := (453994327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393647265851 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393647265851 / 250000000000) = 1/(250000000000 / 393647265851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (226997163 / 500000000) (453994327 / 1000000000) (Real.log (393647265851 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (393647265851 / 250000000000) = -Real.log (250000000000 / 393647265851) := by
    rw [show ((393647265851 / 250000000000) : ℝ) = ((250000000000 / 393647265851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0421
