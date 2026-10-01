import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell045
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

theorem reflection_log_1_neg : (244476869 / 1000000000) ≤ -Real.log (2560 / 3269) ∧
    -Real.log (2560 / 3269) ≤ (24447687 / 100000000) := by
  have h := checkLog_sound (w := (709 / 5829)) (n := 12)
    (lo := (244476869 / 1000000000)) (hi := (24447687 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3269 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3269 / 2560) = 1/(2560 / 3269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (244476869 / 1000000000) (24447687 / 100000000) (Real.log (3269 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3269 / 2560) = -Real.log (2560 / 3269) := by
    rw [show ((3269 / 2560) : ℝ) = ((2560 / 3269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (40535153 / 125000000) ≤ -Real.log (1851 / 2560) ∧
    -Real.log (1851 / 2560) ≤ (12971249 / 40000000) := by
  have h := checkLog_sound (w := (709 / 4411)) (n := 12)
    (lo := (40535153 / 125000000)) (hi := (12971249 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1851) = 1/(1851 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12971249 / 40000000) (-40535153 / 125000000) (Real.log (1851 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (61004477 / 250000000) ≤ -Real.log (1024 / 1307) ∧
    -Real.log (1024 / 1307) ≤ (244017909 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 2331)) (n := 12)
    (lo := (61004477 / 250000000)) (hi := (244017909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1307 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1307 / 1024) = 1/(1024 / 1307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (61004477 / 250000000) (244017909 / 1000000000) (Real.log (1307 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1307 / 1024) = -Real.log (1024 / 1307) := by
    rw [show ((1307 / 1024) : ℝ) = ((1024 / 1307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (16173559 / 50000000) ≤ -Real.log (741 / 1024) ∧
    -Real.log (741 / 1024) ≤ (323471181 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 1765)) (n := 12)
    (lo := (16173559 / 50000000)) (hi := (323471181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 741) = 1/(741 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-323471181 / 1000000000) (-16173559 / 50000000) (Real.log (741 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (179035329 / 1000000000) ≤ -Real.log (1000000 / 1196063) ∧
    -Real.log (1000000 / 1196063) ≤ (17903533 / 100000000) := by
  have h := checkLog_sound (w := (196063 / 2196063)) (n := 12)
    (lo := (179035329 / 1000000000)) (hi := (17903533 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196063 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196063 / 1000000) = 1/(1000000 / 1196063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (179035329 / 1000000000) (17903533 / 100000000) (Real.log (1196063 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1196063 / 1000000) = -Real.log (1000000 / 1196063) := by
    rw [show ((1196063 / 1000000) : ℝ) = ((1000000 / 1196063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (218234371 / 1000000000) ≤ -Real.log (803937 / 1000000) ∧
    -Real.log (803937 / 1000000) ≤ (54558593 / 250000000) := by
  have h := checkLog_sound (w := (196063 / 1803937)) (n := 12)
    (lo := (218234371 / 1000000000)) (hi := (54558593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803937) = 1/(803937 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-54558593 / 250000000) (-218234371 / 1000000000) (Real.log (803937 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (8969321 / 50000000) ≤ -Real.log (1000000 / 1196483) ∧
    -Real.log (1000000 / 1196483) ≤ (179386421 / 1000000000) := by
  have h := checkLog_sound (w := (196483 / 2196483)) (n := 12)
    (lo := (8969321 / 50000000)) (hi := (179386421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196483 / 1000000) = 1/(1000000 / 1196483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (8969321 / 50000000) (179386421 / 1000000000) (Real.log (1196483 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1196483 / 1000000) = -Real.log (1000000 / 1196483) := by
    rw [show ((1196483 / 1000000) : ℝ) = ((1000000 / 1196483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (27344617 / 125000000) ≤ -Real.log (803517 / 1000000) ∧
    -Real.log (803517 / 1000000) ≤ (218756937 / 1000000000) := by
  have h := checkLog_sound (w := (196483 / 1803517)) (n := 12)
    (lo := (27344617 / 125000000)) (hi := (218756937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803517) = 1/(803517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-218756937 / 1000000000) (-27344617 / 125000000) (Real.log (803517 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (13114229 / 100000000) ≤ -Real.log (100000 / 114013) ∧
    -Real.log (100000 / 114013) ≤ (131142291 / 1000000000) := by
  have h := checkLog_sound (w := (14013 / 214013)) (n := 12)
    (lo := (13114229 / 100000000)) (hi := (131142291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114013 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114013 / 100000) = 1/(100000 / 114013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (13114229 / 100000000) (131142291 / 1000000000) (Real.log (114013 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (114013 / 100000) = -Real.log (100000 / 114013) := by
    rw [show ((114013 / 100000) : ℝ) = ((100000 / 114013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (150974063 / 1000000000) ≤ -Real.log (85987 / 100000) ∧
    -Real.log (85987 / 100000) ≤ (9435879 / 62500000) := by
  have h := checkLog_sound (w := (14013 / 185987)) (n := 12)
    (lo := (150974063 / 1000000000)) (hi := (9435879 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 85987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 85987) = 1/(85987 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-9435879 / 62500000) (-150974063 / 1000000000) (Real.log (85987 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (65705761 / 500000000) ≤ -Real.log (1000000 / 1140437) ∧
    -Real.log (1000000 / 1140437) ≤ (131411523 / 1000000000) := by
  have h := checkLog_sound (w := (140437 / 2140437)) (n := 12)
    (lo := (65705761 / 500000000)) (hi := (131411523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1140437 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1140437 / 1000000) = 1/(1000000 / 1140437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (65705761 / 500000000) (131411523 / 1000000000) (Real.log (1140437 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1140437 / 1000000) = -Real.log (1000000 / 1140437) := by
    rw [show ((1140437 / 1000000) : ℝ) = ((1000000 / 1140437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (75665579 / 500000000) ≤ -Real.log (859563 / 1000000) ∧
    -Real.log (859563 / 1000000) ≤ (151331159 / 1000000000) := by
  have h := checkLog_sound (w := (140437 / 1859563)) (n := 12)
    (lo := (75665579 / 500000000)) (hi := (151331159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 859563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 859563) = 1/(859563 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-151331159 / 1000000000) (-75665579 / 500000000) (Real.log (859563 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (8867017 / 15625000) ≤ -Real.log (125000000000 / 220479082321) ∧
    -Real.log (125000000000 / 220479082321) ≤ (567489089 / 1000000000) := by
  have h := checkLog_sound (w := (95479082321 / 345479082321)) (n := 12)
    (lo := (8867017 / 15625000)) (hi := (567489089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220479082321 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(220479082321 / 125000000000) = 1/(125000000000 / 220479082321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (8867017 / 15625000) (567489089 / 1000000000) (Real.log (220479082321 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (220479082321 / 125000000000) = -Real.log (125000000000 / 220479082321) := by
    rw [show ((220479082321 / 125000000000) : ℝ) = ((125000000000 / 220479082321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (284379047 / 500000000) ≤ -Real.log (500000000000 / 883036196651) ∧
    -Real.log (500000000000 / 883036196651) ≤ (113751619 / 200000000) := by
  have h := checkLog_sound (w := (383036196651 / 1383036196651)) (n := 12)
    (lo := (284379047 / 500000000)) (hi := (113751619 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((883036196651 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(883036196651 / 500000000000) = 1/(500000000000 / 883036196651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (284379047 / 500000000) (113751619 / 200000000) (Real.log (883036196651 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (883036196651 / 500000000000) = -Real.log (500000000000 / 883036196651) := by
    rw [show ((883036196651 / 500000000000) : ℝ) = ((500000000000 / 883036196651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (3972697 / 10000000) ≤ -Real.log (500000000000 / 743878562623) ∧
    -Real.log (500000000000 / 743878562623) ≤ (397269701 / 1000000000) := by
  have h := checkLog_sound (w := (243878562623 / 1243878562623)) (n := 12)
    (lo := (3972697 / 10000000)) (hi := (397269701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743878562623 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743878562623 / 500000000000) = 1/(500000000000 / 743878562623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (3972697 / 10000000) (397269701 / 1000000000) (Real.log (743878562623 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (743878562623 / 500000000000) = -Real.log (500000000000 / 743878562623) := by
    rw [show ((743878562623 / 500000000000) : ℝ) = ((500000000000 / 743878562623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (99535839 / 250000000) ≤ -Real.log (20000000000 / 29781149621) ∧
    -Real.log (20000000000 / 29781149621) ≤ (398143357 / 1000000000) := by
  have h := checkLog_sound (w := (9781149621 / 49781149621)) (n := 12)
    (lo := (99535839 / 250000000)) (hi := (398143357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29781149621 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29781149621 / 20000000000) = 1/(20000000000 / 29781149621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (99535839 / 250000000) (398143357 / 1000000000) (Real.log (29781149621 / 20000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (29781149621 / 20000000000) = -Real.log (20000000000 / 29781149621) := by
    rw [show ((29781149621 / 20000000000) : ℝ) = ((20000000000 / 29781149621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (141058177 / 500000000) ≤ -Real.log (100000000000 / 132593298987) ∧
    -Real.log (100000000000 / 132593298987) ≤ (56423271 / 200000000) := by
  have h := checkLog_sound (w := (32593298987 / 232593298987)) (n := 12)
    (lo := (141058177 / 500000000)) (hi := (56423271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132593298987 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132593298987 / 100000000000) = 1/(100000000000 / 132593298987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (141058177 / 500000000) (56423271 / 200000000) (Real.log (132593298987 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (132593298987 / 100000000000) = -Real.log (100000000000 / 132593298987) := by
    rw [show ((132593298987 / 100000000000) : ℝ) = ((100000000000 / 132593298987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (7068567 / 25000000) ≤ -Real.log (500000000000 / 663381857991) ∧
    -Real.log (500000000000 / 663381857991) ≤ (282742681 / 1000000000) := by
  have h := checkLog_sound (w := (163381857991 / 1163381857991)) (n := 12)
    (lo := (7068567 / 25000000)) (hi := (282742681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663381857991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(663381857991 / 500000000000) = 1/(500000000000 / 663381857991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (7068567 / 25000000) (282742681 / 1000000000) (Real.log (663381857991 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (663381857991 / 500000000000) = -Real.log (500000000000 / 663381857991) := by
    rw [show ((663381857991 / 500000000000) : ℝ) = ((500000000000 / 663381857991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4979909 / 250000000) ≤ -Real.log (980277449031 / 1000000000000) ∧
    -Real.log (980277449031 / 1000000000000) ≤ (19919637 / 1000000000) := by
  have h := checkLog_sound (w := (19722550969 / 1980277449031)) (n := 12)
    (lo := (4979909 / 250000000)) (hi := (19919637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980277449031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980277449031) = 1/(980277449031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-19919637 / 1000000000) (-4979909 / 250000000) (Real.log (980277449031 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4957943 / 250000000) ≤ -Real.log (9803635831 / 10000000000) ∧
    -Real.log (9803635831 / 10000000000) ≤ (19831773 / 1000000000) := by
  have h := checkLog_sound (w := (196364169 / 19803635831)) (n := 12)
    (lo := (4957943 / 250000000)) (hi := (19831773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9803635831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9803635831) = 1/(9803635831 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19831773 / 1000000000) (-4957943 / 250000000) (Real.log (9803635831 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell045
