import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell157
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

theorem reflection_log_1_neg : (294591739 / 1000000000) ≤ -Real.log (2560 / 3437) ∧
    -Real.log (2560 / 3437) ≤ (14729587 / 50000000) := by
  have h := checkLog_sound (w := (877 / 5997)) (n := 12)
    (lo := (294591739 / 1000000000)) (hi := (14729587 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3437 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3437 / 2560) = 1/(2560 / 3437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (294591739 / 1000000000) (14729587 / 50000000) (Real.log (3437 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3437 / 2560) = -Real.log (2560 / 3437) := by
    rw [show ((3437 / 2560) : ℝ) = ((2560 / 3437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (419429343 / 1000000000) ≤ -Real.log (1683 / 2560) ∧
    -Real.log (1683 / 2560) ≤ (13107167 / 31250000) := by
  have h := checkLog_sound (w := (877 / 4243)) (n := 12)
    (lo := (419429343 / 1000000000)) (hi := (13107167 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1683) = 1/(1683 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-13107167 / 31250000) (-419429343 / 1000000000) (Real.log (1683 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (18384701 / 62500000) ≤ -Real.log (5120 / 6871) ∧
    -Real.log (5120 / 6871) ≤ (294155217 / 1000000000) := by
  have h := checkLog_sound (w := (1751 / 11991)) (n := 12)
    (lo := (18384701 / 62500000)) (hi := (294155217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6871 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6871 / 5120) = 1/(5120 / 6871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (18384701 / 62500000) (294155217 / 1000000000) (Real.log (6871 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6871 / 5120) = -Real.log (5120 / 6871) := by
    rw [show ((6871 / 5120) : ℝ) = ((5120 / 6871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (209269237 / 500000000) ≤ -Real.log (3369 / 5120) ∧
    -Real.log (3369 / 5120) ≤ (16741539 / 40000000) := by
  have h := checkLog_sound (w := (1751 / 8489)) (n := 12)
    (lo := (209269237 / 500000000)) (hi := (16741539 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3369) = 1/(3369 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-16741539 / 40000000) (-209269237 / 500000000) (Real.log (3369 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (217579299 / 1000000000) ≤ -Real.log (125000 / 155383) ∧
    -Real.log (125000 / 155383) ≤ (2175793 / 10000000) := by
  have h := checkLog_sound (w := (30383 / 280383)) (n := 12)
    (lo := (217579299 / 1000000000)) (hi := (2175793 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155383 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155383 / 125000) = 1/(125000 / 155383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (217579299 / 1000000000) (2175793 / 10000000) (Real.log (155383 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (155383 / 125000) = -Real.log (125000 / 155383) := by
    rw [show ((155383 / 125000) : ℝ) = ((125000 / 155383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (278476573 / 1000000000) ≤ -Real.log (94617 / 125000) ∧
    -Real.log (94617 / 125000) ≤ (139238287 / 500000000) := by
  have h := checkLog_sound (w := (30383 / 219617)) (n := 12)
    (lo := (278476573 / 1000000000)) (hi := (139238287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94617) = 1/(94617 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-139238287 / 500000000) (-278476573 / 1000000000) (Real.log (94617 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (8716749 / 40000000) ≤ -Real.log (500000 / 621743) ∧
    -Real.log (500000 / 621743) ≤ (108959363 / 500000000) := by
  have h := checkLog_sound (w := (121743 / 1121743)) (n := 12)
    (lo := (8716749 / 40000000)) (hi := (108959363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621743 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621743 / 500000) = 1/(500000 / 621743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (8716749 / 40000000) (108959363 / 500000000) (Real.log (621743 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (621743 / 500000) = -Real.log (500000 / 621743) := by
    rw [show ((621743 / 500000) : ℝ) = ((500000 / 621743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (279034239 / 1000000000) ≤ -Real.log (378257 / 500000) ∧
    -Real.log (378257 / 500000) ≤ (435991 / 1562500) := by
  have h := checkLog_sound (w := (121743 / 878257)) (n := 12)
    (lo := (279034239 / 1000000000)) (hi := (435991 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 378257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 378257) = 1/(378257 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-435991 / 1562500) (-279034239 / 1000000000) (Real.log (378257 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (40260009 / 250000000) ≤ -Real.log (250000 / 293683) ∧
    -Real.log (250000 / 293683) ≤ (161040037 / 1000000000) := by
  have h := checkLog_sound (w := (43683 / 543683)) (n := 12)
    (lo := (40260009 / 250000000)) (hi := (161040037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293683 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293683 / 250000) = 1/(250000 / 293683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (40260009 / 250000000) (161040037 / 1000000000) (Real.log (293683 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (293683 / 250000) = -Real.log (250000 / 293683) := by
    rw [show ((293683 / 250000) : ℝ) = ((250000 / 293683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (24005887 / 125000000) ≤ -Real.log (206317 / 250000) ∧
    -Real.log (206317 / 250000) ≤ (192047097 / 1000000000) := by
  have h := checkLog_sound (w := (43683 / 456317)) (n := 12)
    (lo := (24005887 / 125000000)) (hi := (192047097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 206317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 206317) = 1/(206317 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-192047097 / 1000000000) (-24005887 / 125000000) (Real.log (206317 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (32261459 / 200000000) ≤ -Real.log (500000 / 587523) ∧
    -Real.log (500000 / 587523) ≤ (5040853 / 31250000) := by
  have h := checkLog_sound (w := (87523 / 1087523)) (n := 12)
    (lo := (32261459 / 200000000)) (hi := (5040853 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587523 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587523 / 500000) = 1/(500000 / 587523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (32261459 / 200000000) (5040853 / 31250000) (Real.log (587523 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (587523 / 500000) = -Real.log (500000 / 587523) := by
    rw [show ((587523 / 500000) : ℝ) = ((500000 / 587523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (192427651 / 1000000000) ≤ -Real.log (412477 / 500000) ∧
    -Real.log (412477 / 500000) ≤ (48106913 / 250000000) := by
  have h := checkLog_sound (w := (87523 / 912477)) (n := 12)
    (lo := (192427651 / 1000000000)) (hi := (48106913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 412477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 412477) = 1/(412477 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-48106913 / 250000000) (-192427651 / 1000000000) (Real.log (412477 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (712693691 / 1000000000) ≤ -Real.log (250000000000 / 509869397447) ∧
    -Real.log (250000000000 / 509869397447) ≤ (712693693 / 1000000000) := by
  have h := checkLog_sound (w := (9869397447 / 1009869397447)) (n := 12)
    (lo := (19546511 / 1000000000)) (hi := (1221657 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((509869397447 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(509869397447 / 500000000000) = 1/(250000000000 / 509869397447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (712693691 / 1000000000) (712693693 / 1000000000) (Real.log (509869397447 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (509869397447 / 250000000000) = -Real.log (250000000000 / 509869397447) := by
    rw [show ((509869397447 / 250000000000) : ℝ) = ((250000000000 / 509869397447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (357010541 / 500000000) ≤ -Real.log (2500000000 / 5105466429) ∧
    -Real.log (2500000000 / 5105466429) ≤ (178505271 / 250000000) := by
  have h := checkLog_sound (w := (105466429 / 10105466429)) (n := 12)
    (lo := (10436951 / 500000000)) (hi := (20873903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5105466429 / 5000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5105466429 / 5000000000) = 1/(2500000000 / 5105466429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (357010541 / 500000000) (178505271 / 250000000) (Real.log (5105466429 / 2500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (5105466429 / 2500000000) = -Real.log (2500000000 / 5105466429) := by
    rw [show ((5105466429 / 2500000000) : ℝ) = ((2500000000 / 5105466429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (7750873 / 15625000) ≤ -Real.log (125000000000 / 205278913937) ∧
    -Real.log (125000000000 / 205278913937) ≤ (496055873 / 1000000000) := by
  have h := checkLog_sound (w := (80278913937 / 330278913937)) (n := 12)
    (lo := (7750873 / 15625000)) (hi := (496055873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205278913937 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205278913937 / 125000000000) = 1/(125000000000 / 205278913937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (7750873 / 15625000) (496055873 / 1000000000) (Real.log (205278913937 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (205278913937 / 125000000000) = -Real.log (125000000000 / 205278913937) := by
    rw [show ((205278913937 / 125000000000) : ℝ) = ((125000000000 / 205278913937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (99390593 / 200000000) ≤ -Real.log (25000000000 / 41092630143) ∧
    -Real.log (25000000000 / 41092630143) ≤ (248476483 / 500000000) := by
  have h := checkLog_sound (w := (16092630143 / 66092630143)) (n := 12)
    (lo := (99390593 / 200000000)) (hi := (248476483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41092630143 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41092630143 / 25000000000) = 1/(25000000000 / 41092630143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (99390593 / 200000000) (248476483 / 500000000) (Real.log (41092630143 / 25000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (41092630143 / 25000000000) = -Real.log (25000000000 / 41092630143) := by
    rw [show ((41092630143 / 25000000000) : ℝ) = ((25000000000 / 41092630143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (353087133 / 1000000000) ≤ -Real.log (500000000000 / 711727584251) ∧
    -Real.log (500000000000 / 711727584251) ≤ (176543567 / 500000000) := by
  have h := checkLog_sound (w := (211727584251 / 1211727584251)) (n := 12)
    (lo := (353087133 / 1000000000)) (hi := (176543567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711727584251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711727584251 / 500000000000) = 1/(500000000000 / 711727584251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (353087133 / 1000000000) (176543567 / 500000000) (Real.log (711727584251 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (711727584251 / 500000000000) = -Real.log (500000000000 / 711727584251) := by
    rw [show ((711727584251 / 500000000000) : ℝ) = ((500000000000 / 711727584251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (353734947 / 1000000000) ≤ -Real.log (500000000000 / 712188800831) ∧
    -Real.log (500000000000 / 712188800831) ≤ (88433737 / 250000000) := by
  have h := checkLog_sound (w := (212188800831 / 1212188800831)) (n := 12)
    (lo := (353734947 / 1000000000)) (hi := (88433737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712188800831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712188800831 / 500000000000) = 1/(500000000000 / 712188800831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (353734947 / 1000000000) (88433737 / 250000000) (Real.log (712188800831 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (712188800831 / 500000000000) = -Real.log (500000000000 / 712188800831) := by
    rw [show ((712188800831 / 500000000000) : ℝ) = ((500000000000 / 712188800831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7780089 / 250000000) ≤ -Real.log (242339724471 / 250000000000) ∧
    -Real.log (242339724471 / 250000000000) ≤ (31120357 / 1000000000) := by
  have h := checkLog_sound (w := (7660275529 / 492339724471)) (n := 12)
    (lo := (7780089 / 250000000)) (hi := (31120357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242339724471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242339724471) = 1/(242339724471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-31120357 / 1000000000) (-7780089 / 250000000) (Real.log (242339724471 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1550353 / 50000000) ≤ -Real.log (60591795511 / 62500000000) ∧
    -Real.log (60591795511 / 62500000000) ≤ (31007061 / 1000000000) := by
  have h := checkLog_sound (w := (1908204489 / 123091795511)) (n := 12)
    (lo := (1550353 / 50000000)) (hi := (31007061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60591795511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60591795511) = 1/(60591795511 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-31007061 / 1000000000) (-1550353 / 50000000) (Real.log (60591795511 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell157
