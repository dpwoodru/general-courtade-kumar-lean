import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0225
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

theorem reflection_log_1_neg : (246012497 / 500000000) ≤ -Real.log (1600 / 2617) ∧
    -Real.log (1600 / 2617) ≤ (98404999 / 200000000) := by
  have h := checkLog_sound (w := (1017 / 4217)) (n := 12)
    (lo := (246012497 / 500000000)) (hi := (98404999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2617 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2617 / 1600) = 1/(1600 / 2617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (246012497 / 500000000) (98404999 / 200000000) (Real.log (2617 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2617 / 1600) = -Real.log (1600 / 2617) := by
    rw [show ((2617 / 1600) : ℝ) = ((1600 / 2617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1009571721 / 1000000000) ≤ -Real.log (583 / 1600) ∧
    -Real.log (583 / 1600) ≤ (1009571723 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1383)) (n := 12)
    (lo := (316424541 / 1000000000)) (hi := (158212271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 583) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 583) = 1/(583 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1009571723 / 1000000000) (-1009571721 / 1000000000) (Real.log (583 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (484738289 / 1000000000) ≤ -Real.log (800 / 1299) ∧
    -Real.log (800 / 1299) ≤ (48473829 / 100000000) := by
  have h := checkLog_sound (w := (499 / 2099)) (n := 12)
    (lo := (484738289 / 1000000000)) (hi := (48473829 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299 / 800) = 1/(800 / 1299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (484738289 / 1000000000) (48473829 / 100000000) (Real.log (1299 / 800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1299 / 800) = -Real.log (800 / 1299) := by
    rw [show ((1299 / 800) : ℝ) = ((800 / 1299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (488750731 / 500000000) ≤ -Real.log (301 / 800) ∧
    -Real.log (301 / 800) ≤ (122187683 / 125000000) := by
  have h := checkLog_sound (w := (99 / 701)) (n := 12)
    (lo := (142177141 / 500000000)) (hi := (284354283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 301) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 301) = 1/(301 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-122187683 / 125000000) (-488750731 / 500000000) (Real.log (301 / 800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (60000167 / 250000000) ≤ -Real.log (800 / 1017) ∧
    -Real.log (800 / 1017) ≤ (240000669 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1817)) (n := 12)
    (lo := (60000167 / 250000000)) (hi := (240000669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1017 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1017 / 800) = 1/(800 / 1017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (60000167 / 250000000) (240000669 / 1000000000) (Real.log (1017 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1017 / 800) = -Real.log (800 / 1017) := by
    rw [show ((1017 / 800) : ℝ) = ((800 / 1017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (316424541 / 1000000000) ≤ -Real.log (583 / 800) ∧
    -Real.log (583 / 800) ≤ (158212271 / 500000000) := by
  have h := checkLog_sound (w := (217 / 1383)) (n := 12)
    (lo := (316424541 / 1000000000)) (hi := (158212271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 583) = 1/(583 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-158212271 / 500000000) (-316424541 / 1000000000) (Real.log (583 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (55285387 / 250000000) ≤ -Real.log (400 / 499) ∧
    -Real.log (400 / 499) ≤ (221141549 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 899)) (n := 12)
    (lo := (55285387 / 250000000)) (hi := (221141549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(499 / 400) = 1/(400 / 499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (55285387 / 250000000) (221141549 / 1000000000) (Real.log (499 / 400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (499 / 400) = -Real.log (400 / 499) := by
    rw [show ((499 / 400) : ℝ) = ((400 / 499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (142177141 / 500000000) ≤ -Real.log (301 / 400) ∧
    -Real.log (301 / 400) ≤ (284354283 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 701)) (n := 12)
    (lo := (142177141 / 500000000)) (hi := (284354283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 301) = 1/(301 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-284354283 / 1000000000) (-142177141 / 500000000) (Real.log (301 / 400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (73089759 / 125000000) ≤ -Real.log (200000 / 358897) ∧
    -Real.log (200000 / 358897) ≤ (584718073 / 1000000000) := by
  have h := checkLog_sound (w := (158897 / 558897)) (n := 12)
    (lo := (73089759 / 125000000)) (hi := (584718073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358897 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358897 / 200000) = 1/(200000 / 358897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (73089759 / 125000000) (584718073 / 1000000000) (Real.log (358897 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (358897 / 200000) = -Real.log (200000 / 358897) := by
    rw [show ((358897 / 200000) : ℝ) = ((200000 / 358897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1582236253 / 1000000000) ≤ -Real.log (41103 / 200000) ∧
    -Real.log (41103 / 200000) ≤ (49444883 / 31250000) := by
  have h := checkLog_sound (w := (8897 / 91103)) (n := 12)
    (lo := (195941893 / 1000000000)) (hi := (97970947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 41103) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 41103) = 1/(41103 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-49444883 / 31250000) (-1582236253 / 1000000000) (Real.log (41103 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (58633283 / 100000000) ≤ -Real.log (200000 / 359477) ∧
    -Real.log (200000 / 359477) ≤ (586332831 / 1000000000) := by
  have h := checkLog_sound (w := (159477 / 559477)) (n := 12)
    (lo := (58633283 / 100000000)) (hi := (586332831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359477 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359477 / 200000) = 1/(200000 / 359477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (58633283 / 100000000) (586332831 / 1000000000) (Real.log (359477 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (359477 / 200000) = -Real.log (200000 / 359477) := by
    rw [show ((359477 / 200000) : ℝ) = ((200000 / 359477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1596447651 / 1000000000) ≤ -Real.log (40523 / 200000) ∧
    -Real.log (40523 / 200000) ≤ (798223827 / 500000000) := by
  have h := checkLog_sound (w := (9477 / 90523)) (n := 12)
    (lo := (210153291 / 1000000000)) (hi := (52538323 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40523) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 40523) = 1/(40523 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-798223827 / 500000000) (-1596447651 / 1000000000) (Real.log (40523 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (551382559 / 1000000000) ≤ -Real.log (1000000 / 1735651) ∧
    -Real.log (1000000 / 1735651) ≤ (3446141 / 6250000) := by
  have h := checkLog_sound (w := (735651 / 2735651)) (n := 12)
    (lo := (551382559 / 1000000000)) (hi := (3446141 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1735651 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1735651 / 1000000) = 1/(1000000 / 1735651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (551382559 / 1000000000) (3446141 / 6250000) (Real.log (1735651 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1735651 / 1000000) = -Real.log (1000000 / 1735651) := by
    rw [show ((1735651 / 1000000) : ℝ) = ((1000000 / 1735651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (665242539 / 500000000) ≤ -Real.log (264349 / 1000000) ∧
    -Real.log (264349 / 1000000) ≤ (33262127 / 25000000) := by
  have h := checkLog_sound (w := (235651 / 764349)) (n := 12)
    (lo := (318668949 / 500000000)) (hi := (637337899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 264349) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 264349) = 1/(264349 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-33262127 / 25000000) (-665242539 / 500000000) (Real.log (264349 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (277838879 / 500000000) ≤ -Real.log (500000 / 871561) ∧
    -Real.log (500000 / 871561) ≤ (555677759 / 1000000000) := by
  have h := checkLog_sound (w := (371561 / 1371561)) (n := 12)
    (lo := (277838879 / 500000000)) (hi := (555677759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871561 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(871561 / 500000) = 1/(500000 / 871561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (277838879 / 500000000) (555677759 / 1000000000) (Real.log (871561 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (871561 / 500000) = -Real.log (500000 / 871561) := by
    rw [show ((871561 / 500000) : ℝ) = ((500000 / 871561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (679577007 / 500000000) ≤ -Real.log (128439 / 500000) ∧
    -Real.log (128439 / 500000) ≤ (42473563 / 31250000) := by
  have h := checkLog_sound (w := (121561 / 378439)) (n := 12)
    (lo := (333003417 / 500000000)) (hi := (133201367 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 128439) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 128439) = 1/(128439 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-42473563 / 31250000) (-679577007 / 500000000) (Real.log (128439 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1083477163 / 500000000) ≤ -Real.log (250000000000 / 2182912439481) ∧
    -Real.log (250000000000 / 2182912439481) ≤ (216695433 / 100000000) := by
  have h := checkLog_sound (w := (182912439481 / 4182912439481)) (n := 12)
    (lo := (43756393 / 500000000)) (hi := (87512787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2182912439481 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2182912439481 / 2000000000000) = 1/(250000000000 / 2182912439481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1083477163 / 500000000) (216695433 / 100000000) (Real.log (2182912439481 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2182912439481 / 250000000000) = -Real.log (250000000000 / 2182912439481) := by
    rw [show ((2182912439481 / 250000000000) : ℝ) = ((250000000000 / 2182912439481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2182780481 / 1000000000) ≤ -Real.log (100000000000 / 887093749229) ∧
    -Real.log (100000000000 / 887093749229) ≤ (436556097 / 200000000) := by
  have h := checkLog_sound (w := (87093749229 / 1687093749229)) (n := 12)
    (lo := (103338941 / 1000000000)) (hi := (51669471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887093749229 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(887093749229 / 800000000000) = 1/(100000000000 / 887093749229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2182780481 / 1000000000) (436556097 / 200000000) (Real.log (887093749229 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (887093749229 / 100000000000) = -Real.log (100000000000 / 887093749229) := by
    rw [show ((887093749229 / 100000000000) : ℝ) = ((100000000000 / 887093749229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1881867637 / 1000000000) ≤ -Real.log (500000000000 / 3282877937877) ∧
    -Real.log (500000000000 / 3282877937877) ≤ (47046691 / 25000000) := by
  have h := checkLog_sound (w := (1282877937877 / 5282877937877)) (n := 12)
    (lo := (495573277 / 1000000000)) (hi := (247786639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3282877937877 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3282877937877 / 2000000000000) = 1/(500000000000 / 3282877937877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1881867637 / 1000000000) (47046691 / 25000000) (Real.log (3282877937877 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3282877937877 / 500000000000) = -Real.log (500000000000 / 3282877937877) := by
    rw [show ((3282877937877 / 500000000000) : ℝ) = ((500000000000 / 3282877937877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (478707943 / 250000000) ≤ -Real.log (500000000000 / 3392898574421) ∧
    -Real.log (500000000000 / 3392898574421) ≤ (76593271 / 40000000) := by
  have h := checkLog_sound (w := (1392898574421 / 5392898574421)) (n := 12)
    (lo := (132134353 / 250000000)) (hi := (528537413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3392898574421 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3392898574421 / 2000000000000) = 1/(500000000000 / 3392898574421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (478707943 / 250000000) (76593271 / 40000000) (Real.log (3392898574421 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3392898574421 / 500000000000) = -Real.log (500000000000 / 3392898574421) := by
    rw [show ((3392898574421 / 500000000000) : ℝ) = ((500000000000 / 3392898574421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0225
