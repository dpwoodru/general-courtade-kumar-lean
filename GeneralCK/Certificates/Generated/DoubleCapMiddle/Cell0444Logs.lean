import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0444
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

theorem reflection_log_1_neg : (189619083 / 1000000000) ≤ -Real.log (5120 / 6189) ∧
    -Real.log (5120 / 6189) ≤ (47404771 / 250000000) := by
  have h := checkLog_sound (w := (1069 / 11309)) (n := 12)
    (lo := (189619083 / 1000000000)) (hi := (47404771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6189 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6189 / 5120) = 1/(5120 / 6189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (189619083 / 1000000000) (47404771 / 250000000) (Real.log (6189 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6189 / 5120) = -Real.log (5120 / 6189) := by
    rw [show ((6189 / 5120) : ℝ) = ((5120 / 6189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (117095337 / 500000000) ≤ -Real.log (4051 / 5120) ∧
    -Real.log (4051 / 5120) ≤ (9367627 / 40000000) := by
  have h := checkLog_sound (w := (1069 / 9171)) (n := 12)
    (lo := (117095337 / 500000000)) (hi := (9367627 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4051) = 1/(4051 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-9367627 / 40000000) (-117095337 / 500000000) (Real.log (4051 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11836043 / 62500000) ≤ -Real.log (2048 / 2475) ∧
    -Real.log (2048 / 2475) ≤ (189376689 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 4523)) (n := 12)
    (lo := (11836043 / 62500000)) (hi := (189376689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2475 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2475 / 2048) = 1/(2048 / 2475) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11836043 / 62500000) (189376689 / 1000000000) (Real.log (2475 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2475 / 2048) = -Real.log (2048 / 2475) := by
    rw [show ((2475 / 2048) : ℝ) = ((2048 / 2475) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (14613779 / 62500000) ≤ -Real.log (1621 / 2048) ∧
    -Real.log (1621 / 2048) ≤ (46764093 / 200000000) := by
  have h := checkLog_sound (w := (427 / 3669)) (n := 12)
    (lo := (14613779 / 62500000)) (hi := (46764093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1621) = 1/(1621 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-46764093 / 200000000) (-14613779 / 62500000) (Real.log (1621 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (348949869 / 1000000000) ≤ -Real.log (2560 / 3629) ∧
    -Real.log (2560 / 3629) ≤ (34894987 / 100000000) := by
  have h := checkLog_sound (w := (1069 / 6189)) (n := 12)
    (lo := (348949869 / 1000000000)) (hi := (34894987 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3629 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3629 / 2560) = 1/(2560 / 3629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (348949869 / 1000000000) (34894987 / 100000000) (Real.log (3629 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3629 / 2560) = -Real.log (2560 / 3629) := by
    rw [show ((3629 / 2560) : ℝ) = ((2560 / 3629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (270280111 / 500000000) ≤ -Real.log (1491 / 2560) ∧
    -Real.log (1491 / 2560) ≤ (540560223 / 1000000000) := by
  have h := checkLog_sound (w := (1069 / 4051)) (n := 12)
    (lo := (270280111 / 500000000)) (hi := (540560223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1491) = 1/(1491 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-540560223 / 1000000000) (-270280111 / 500000000) (Real.log (1491 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (348536447 / 1000000000) ≤ -Real.log (1024 / 1451) ∧
    -Real.log (1024 / 1451) ≤ (2722941 / 7812500) := by
  have h := checkLog_sound (w := (427 / 2475)) (n := 12)
    (lo := (348536447 / 1000000000)) (hi := (2722941 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1451 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1451 / 1024) = 1/(1024 / 1451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (348536447 / 1000000000) (2722941 / 7812500) (Real.log (1451 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1451 / 1024) = -Real.log (1024 / 1451) := by
    rw [show ((1451 / 1024) : ℝ) = ((1024 / 1451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (134888673 / 250000000) ≤ -Real.log (597 / 1024) ∧
    -Real.log (597 / 1024) ≤ (539554693 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 1621)) (n := 12)
    (lo := (134888673 / 250000000)) (hi := (539554693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 597) = 1/(597 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-539554693 / 1000000000) (-134888673 / 250000000) (Real.log (597 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (130090171 / 500000000) ≤ -Real.log (250000 / 324291) ∧
    -Real.log (250000 / 324291) ≤ (260180343 / 1000000000) := by
  have h := checkLog_sound (w := (74291 / 574291)) (n := 12)
    (lo := (130090171 / 500000000)) (hi := (260180343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324291 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(324291 / 250000) = 1/(250000 / 324291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (130090171 / 500000000) (260180343 / 1000000000) (Real.log (324291 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (324291 / 250000) = -Real.log (250000 / 324291) := by
    rw [show ((324291 / 250000) : ℝ) = ((250000 / 324291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3526317 / 10000000) ≤ -Real.log (175709 / 250000) ∧
    -Real.log (175709 / 250000) ≤ (352631701 / 1000000000) := by
  have h := checkLog_sound (w := (74291 / 425709)) (n := 12)
    (lo := (3526317 / 10000000)) (hi := (352631701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 175709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 175709) = 1/(175709 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-352631701 / 1000000000) (-3526317 / 10000000) (Real.log (175709 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (260507927 / 1000000000) ≤ -Real.log (1000000 / 1297589) ∧
    -Real.log (1000000 / 1297589) ≤ (32563491 / 125000000) := by
  have h := checkLog_sound (w := (297589 / 2297589)) (n := 12)
    (lo := (260507927 / 1000000000)) (hi := (32563491 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1297589 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1297589 / 1000000) = 1/(1000000 / 1297589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (260507927 / 1000000000) (32563491 / 125000000) (Real.log (1297589 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1297589 / 1000000) = -Real.log (1000000 / 1297589) := by
    rw [show ((1297589 / 1000000) : ℝ) = ((1000000 / 1297589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (11038643 / 31250000) ≤ -Real.log (702411 / 1000000) ∧
    -Real.log (702411 / 1000000) ≤ (353236577 / 1000000000) := by
  have h := checkLog_sound (w := (297589 / 1702411)) (n := 12)
    (lo := (11038643 / 31250000)) (hi := (353236577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 702411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 702411) = 1/(702411 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-353236577 / 1000000000) (-11038643 / 31250000) (Real.log (702411 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (195067481 / 1000000000) ≤ -Real.log (1000000 / 1215393) ∧
    -Real.log (1000000 / 1215393) ≤ (97533741 / 500000000) := by
  have h := checkLog_sound (w := (215393 / 2215393)) (n := 12)
    (lo := (195067481 / 1000000000)) (hi := (97533741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1215393 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1215393 / 1000000) = 1/(1000000 / 1215393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (195067481 / 1000000000) (97533741 / 500000000) (Real.log (1215393 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1215393 / 1000000) = -Real.log (1000000 / 1215393) := by
    rw [show ((1215393 / 1000000) : ℝ) = ((1000000 / 1215393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (242572323 / 1000000000) ≤ -Real.log (784607 / 1000000) ∧
    -Real.log (784607 / 1000000) ≤ (60643081 / 250000000) := by
  have h := checkLog_sound (w := (215393 / 1784607)) (n := 12)
    (lo := (242572323 / 1000000000)) (hi := (60643081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 784607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 784607) = 1/(784607 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-60643081 / 250000000) (-242572323 / 1000000000) (Real.log (784607 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (97667013 / 500000000) ≤ -Real.log (1000000 / 1215717) ∧
    -Real.log (1000000 / 1215717) ≤ (195334027 / 1000000000) := by
  have h := checkLog_sound (w := (215717 / 2215717)) (n := 12)
    (lo := (97667013 / 500000000)) (hi := (195334027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1215717 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1215717 / 1000000) = 1/(1000000 / 1215717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (97667013 / 500000000) (195334027 / 1000000000) (Real.log (1215717 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1215717 / 1000000) = -Real.log (1000000 / 1215717) := by
    rw [show ((1215717 / 1000000) : ℝ) = ((1000000 / 1215717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (121492677 / 500000000) ≤ -Real.log (784283 / 1000000) ∧
    -Real.log (784283 / 1000000) ≤ (48597071 / 200000000) := by
  have h := checkLog_sound (w := (215717 / 1784283)) (n := 12)
    (lo := (121492677 / 500000000)) (hi := (48597071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 784283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 784283) = 1/(784283 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-48597071 / 200000000) (-121492677 / 500000000) (Real.log (784283 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (612812043 / 1000000000) ≤ -Real.log (62500000000 / 115350878441) ∧
    -Real.log (62500000000 / 115350878441) ≤ (153203011 / 250000000) := by
  have h := checkLog_sound (w := (52850878441 / 177850878441)) (n := 12)
    (lo := (612812043 / 1000000000)) (hi := (153203011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115350878441 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115350878441 / 62500000000) = 1/(62500000000 / 115350878441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (612812043 / 1000000000) (153203011 / 250000000) (Real.log (115350878441 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (115350878441 / 62500000000) = -Real.log (62500000000 / 115350878441) := by
    rw [show ((115350878441 / 62500000000) : ℝ) = ((62500000000 / 115350878441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (613744503 / 1000000000) ≤ -Real.log (500000000000 / 923667909529) ∧
    -Real.log (500000000000 / 923667909529) ≤ (76718063 / 125000000) := by
  have h := checkLog_sound (w := (423667909529 / 1423667909529)) (n := 12)
    (lo := (613744503 / 1000000000)) (hi := (76718063 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((923667909529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(923667909529 / 500000000000) = 1/(500000000000 / 923667909529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (613744503 / 1000000000) (76718063 / 125000000) (Real.log (923667909529 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (923667909529 / 500000000000) = -Real.log (500000000000 / 923667909529) := by
    rw [show ((923667909529 / 500000000000) : ℝ) = ((500000000000 / 923667909529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (109409951 / 250000000) ≤ -Real.log (125000000000 / 193630855957) ∧
    -Real.log (125000000000 / 193630855957) ≤ (87527961 / 200000000) := by
  have h := checkLog_sound (w := (68630855957 / 318630855957)) (n := 12)
    (lo := (109409951 / 250000000)) (hi := (87527961 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193630855957 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193630855957 / 125000000000) = 1/(125000000000 / 193630855957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (109409951 / 250000000) (87527961 / 200000000) (Real.log (193630855957 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (193630855957 / 125000000000) = -Real.log (125000000000 / 193630855957) := by
    rw [show ((193630855957 / 125000000000) : ℝ) = ((125000000000 / 193630855957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (21915969 / 50000000) ≤ -Real.log (250000000000 / 387524975041) ∧
    -Real.log (250000000000 / 387524975041) ≤ (438319381 / 1000000000) := by
  have h := checkLog_sound (w := (137524975041 / 637524975041)) (n := 12)
    (lo := (21915969 / 50000000)) (hi := (438319381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387524975041 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387524975041 / 250000000000) = 1/(250000000000 / 387524975041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (21915969 / 50000000) (438319381 / 1000000000) (Real.log (387524975041 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (387524975041 / 250000000000) = -Real.log (250000000000 / 387524975041) := by
    rw [show ((387524975041 / 250000000000) : ℝ) = ((250000000000 / 387524975041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0444
