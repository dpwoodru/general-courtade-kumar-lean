import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell073
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

theorem reflection_log_1_neg : (257243 / 1000000) ≤ -Real.log (2560 / 3311) ∧
    -Real.log (2560 / 3311) ≤ (257243001 / 1000000000) := by
  have h := checkLog_sound (w := (751 / 5871)) (n := 12)
    (lo := (257243 / 1000000)) (hi := (257243001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3311 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3311 / 2560) = 1/(2560 / 3311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (257243 / 1000000) (257243001 / 1000000000) (Real.log (3311 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3311 / 2560) = -Real.log (2560 / 3311) := by
    rw [show ((3311 / 2560) : ℝ) = ((2560 / 3311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (86808263 / 250000000) ≤ -Real.log (1809 / 2560) ∧
    -Real.log (1809 / 2560) ≤ (347233053 / 1000000000) := by
  have h := checkLog_sound (w := (751 / 4369)) (n := 12)
    (lo := (86808263 / 250000000)) (hi := (347233053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1809) = 1/(1809 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-347233053 / 1000000000) (-86808263 / 250000000) (Real.log (1809 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128394931 / 500000000) ≤ -Real.log (5120 / 6619) ∧
    -Real.log (5120 / 6619) ≤ (256789863 / 1000000000) := by
  have h := checkLog_sound (w := (1499 / 11739)) (n := 12)
    (lo := (128394931 / 500000000)) (hi := (256789863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6619 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6619 / 5120) = 1/(5120 / 6619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128394931 / 500000000) (256789863 / 1000000000) (Real.log (6619 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6619 / 5120) = -Real.log (5120 / 6619) := by
    rw [show ((6619 / 5120) : ℝ) = ((5120 / 6619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (21650263 / 62500000) ≤ -Real.log (3621 / 5120) ∧
    -Real.log (3621 / 5120) ≤ (346404209 / 1000000000) := by
  have h := checkLog_sound (w := (1499 / 8741)) (n := 12)
    (lo := (21650263 / 62500000)) (hi := (346404209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3621) = 1/(3621 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-346404209 / 1000000000) (-21650263 / 62500000) (Real.log (3621 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (188790587 / 1000000000) ≤ -Real.log (250000 / 301947) ∧
    -Real.log (250000 / 301947) ≤ (47197647 / 250000000) := by
  have h := checkLog_sound (w := (51947 / 551947)) (n := 12)
    (lo := (188790587 / 1000000000)) (hi := (47197647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301947 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301947 / 250000) = 1/(250000 / 301947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (188790587 / 1000000000) (47197647 / 250000000) (Real.log (301947 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (301947 / 250000) = -Real.log (250000 / 301947) := by
    rw [show ((301947 / 250000) : ℝ) = ((250000 / 301947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (116463123 / 500000000) ≤ -Real.log (198053 / 250000) ∧
    -Real.log (198053 / 250000) ≤ (232926247 / 1000000000) := by
  have h := checkLog_sound (w := (51947 / 448053)) (n := 12)
    (lo := (116463123 / 500000000)) (hi := (232926247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 198053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 198053) = 1/(198053 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-232926247 / 1000000000) (-116463123 / 500000000) (Real.log (198053 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (18913827 / 100000000) ≤ -Real.log (62500 / 75513) ∧
    -Real.log (62500 / 75513) ≤ (189138271 / 1000000000) := by
  have h := checkLog_sound (w := (13013 / 138013)) (n := 12)
    (lo := (18913827 / 100000000)) (hi := (189138271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75513 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75513 / 62500) = 1/(62500 / 75513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (18913827 / 100000000) (189138271 / 1000000000) (Real.log (75513 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (75513 / 62500) = -Real.log (62500 / 75513) := by
    rw [show ((75513 / 62500) : ℝ) = ((62500 / 75513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (233456547 / 1000000000) ≤ -Real.log (49487 / 62500) ∧
    -Real.log (49487 / 62500) ≤ (58364137 / 250000000) := by
  have h := checkLog_sound (w := (13013 / 111987)) (n := 12)
    (lo := (233456547 / 1000000000)) (hi := (58364137 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49487) = 1/(49487 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-58364137 / 250000000) (-233456547 / 1000000000) (Real.log (49487 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (17329729 / 125000000) ≤ -Real.log (250000 / 287177) ∧
    -Real.log (250000 / 287177) ≤ (138637833 / 1000000000) := by
  have h := checkLog_sound (w := (37177 / 537177)) (n := 12)
    (lo := (17329729 / 125000000)) (hi := (138637833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287177 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287177 / 250000) = 1/(250000 / 287177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (17329729 / 125000000) (138637833 / 1000000000) (Real.log (287177 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (287177 / 250000) = -Real.log (250000 / 287177) := by
    rw [show ((287177 / 250000) : ℝ) = ((250000 / 287177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (161000083 / 1000000000) ≤ -Real.log (212823 / 250000) ∧
    -Real.log (212823 / 250000) ≤ (40250021 / 250000000) := by
  have h := checkLog_sound (w := (37177 / 462823)) (n := 12)
    (lo := (161000083 / 1000000000)) (hi := (40250021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 212823) = 1/(212823 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-40250021 / 250000000) (-161000083 / 1000000000) (Real.log (212823 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (138905923 / 1000000000) ≤ -Real.log (125000 / 143627) ∧
    -Real.log (125000 / 143627) ≤ (34726481 / 250000000) := by
  have h := checkLog_sound (w := (18627 / 268627)) (n := 12)
    (lo := (138905923 / 1000000000)) (hi := (34726481 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143627 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143627 / 125000) = 1/(125000 / 143627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (138905923 / 1000000000) (34726481 / 250000000) (Real.log (143627 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (143627 / 125000) = -Real.log (125000 / 143627) := by
    rw [show ((143627 / 125000) : ℝ) = ((125000 / 143627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (161361951 / 1000000000) ≤ -Real.log (106373 / 125000) ∧
    -Real.log (106373 / 125000) ≤ (5042561 / 31250000) := by
  have h := checkLog_sound (w := (18627 / 231373)) (n := 12)
    (lo := (161361951 / 1000000000)) (hi := (5042561 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 106373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 106373) = 1/(106373 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-5042561 / 31250000) (-161361951 / 1000000000) (Real.log (106373 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (60319407 / 100000000) ≤ -Real.log (390625000 / 714042219) ∧
    -Real.log (390625000 / 714042219) ≤ (603194071 / 1000000000) := by
  have h := checkLog_sound (w := (323417219 / 1104667219)) (n := 12)
    (lo := (60319407 / 100000000)) (hi := (603194071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714042219 / 390625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714042219 / 390625000) = 1/(390625000 / 714042219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (60319407 / 100000000) (603194071 / 1000000000) (Real.log (714042219 / 390625000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (714042219 / 390625000) = -Real.log (390625000 / 714042219) := by
    rw [show ((714042219 / 390625000) : ℝ) = ((390625000 / 714042219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (151119013 / 250000000) ≤ -Real.log (250000000000 / 457573244887) ∧
    -Real.log (250000000000 / 457573244887) ≤ (604476053 / 1000000000) := by
  have h := checkLog_sound (w := (207573244887 / 707573244887)) (n := 12)
    (lo := (151119013 / 250000000)) (hi := (604476053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457573244887 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(457573244887 / 250000000000) = 1/(250000000000 / 457573244887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (151119013 / 250000000) (604476053 / 1000000000) (Real.log (457573244887 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (457573244887 / 250000000000) = -Real.log (250000000000 / 457573244887) := by
    rw [show ((457573244887 / 250000000000) : ℝ) = ((250000000000 / 457573244887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (421716833 / 1000000000) ≤ -Real.log (500000000000 / 762288377353) ∧
    -Real.log (500000000000 / 762288377353) ≤ (210858417 / 500000000) := by
  have h := checkLog_sound (w := (262288377353 / 1262288377353)) (n := 12)
    (lo := (421716833 / 1000000000)) (hi := (210858417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((762288377353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(762288377353 / 500000000000) = 1/(500000000000 / 762288377353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (421716833 / 1000000000) (210858417 / 500000000) (Real.log (762288377353 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (762288377353 / 500000000000) = -Real.log (500000000000 / 762288377353) := by
    rw [show ((762288377353 / 500000000000) : ℝ) = ((500000000000 / 762288377353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (211297409 / 500000000) ≤ -Real.log (500000000000 / 762957948553) ∧
    -Real.log (500000000000 / 762957948553) ≤ (422594819 / 1000000000) := by
  have h := checkLog_sound (w := (262957948553 / 1262957948553)) (n := 12)
    (lo := (211297409 / 500000000)) (hi := (422594819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((762957948553 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(762957948553 / 500000000000) = 1/(500000000000 / 762957948553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (211297409 / 500000000) (422594819 / 1000000000) (Real.log (762957948553 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (762957948553 / 500000000000) = -Real.log (500000000000 / 762957948553) := by
    rw [show ((762957948553 / 500000000000) : ℝ) = ((500000000000 / 762957948553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (74909479 / 250000000) ≤ -Real.log (500000000000 / 674685066933) ∧
    -Real.log (500000000000 / 674685066933) ≤ (299637917 / 1000000000) := by
  have h := checkLog_sound (w := (174685066933 / 1174685066933)) (n := 12)
    (lo := (74909479 / 250000000)) (hi := (299637917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((674685066933 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(674685066933 / 500000000000) = 1/(500000000000 / 674685066933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (74909479 / 250000000) (299637917 / 1000000000) (Real.log (674685066933 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (674685066933 / 500000000000) = -Real.log (500000000000 / 674685066933) := by
    rw [show ((674685066933 / 500000000000) : ℝ) = ((500000000000 / 674685066933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2402143 / 8000000) ≤ -Real.log (25000000000 / 33755511267) ∧
    -Real.log (25000000000 / 33755511267) ≤ (75066969 / 250000000) := by
  have h := checkLog_sound (w := (8755511267 / 58755511267)) (n := 12)
    (lo := (2402143 / 8000000)) (hi := (75066969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33755511267 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33755511267 / 25000000000) = 1/(25000000000 / 33755511267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2402143 / 8000000) (75066969 / 250000000) (Real.log (33755511267 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (33755511267 / 25000000000) = -Real.log (25000000000 / 33755511267) := by
    rw [show ((33755511267 / 25000000000) : ℝ) = ((25000000000 / 33755511267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5614007 / 250000000) ≤ -Real.log (15278034871 / 15625000000) ∧
    -Real.log (15278034871 / 15625000000) ≤ (22456029 / 1000000000) := by
  have h := checkLog_sound (w := (346965129 / 30903034871)) (n := 12)
    (lo := (5614007 / 250000000)) (hi := (22456029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15278034871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15278034871) = 1/(15278034871 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-22456029 / 1000000000) (-5614007 / 250000000) (Real.log (15278034871 / 15625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (89449 / 4000000) ≤ -Real.log (61117870671 / 62500000000) ∧
    -Real.log (61117870671 / 62500000000) ≤ (22362251 / 1000000000) := by
  have h := checkLog_sound (w := (1382129329 / 123617870671)) (n := 12)
    (lo := (89449 / 4000000)) (hi := (22362251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61117870671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61117870671) = 1/(61117870671 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-22362251 / 1000000000) (-89449 / 4000000) (Real.log (61117870671 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell073
