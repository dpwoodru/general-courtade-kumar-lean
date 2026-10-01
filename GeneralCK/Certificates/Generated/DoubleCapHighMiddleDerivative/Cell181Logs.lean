import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell181
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

theorem reflection_log_1_neg : (61002303 / 200000000) ≤ -Real.log (2560 / 3473) ∧
    -Real.log (2560 / 3473) ≤ (76252879 / 250000000) := by
  have h := checkLog_sound (w := (913 / 6033)) (n := 12)
    (lo := (61002303 / 200000000)) (hi := (76252879 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3473 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3473 / 2560) = 1/(2560 / 3473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (61002303 / 200000000) (76252879 / 250000000) (Real.log (3473 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3473 / 2560) = -Real.log (2560 / 3473) := by
    rw [show ((3473 / 2560) : ℝ) = ((2560 / 3473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (441051807 / 1000000000) ≤ -Real.log (1647 / 2560) ∧
    -Real.log (1647 / 2560) ≤ (13782869 / 31250000) := by
  have h := checkLog_sound (w := (913 / 4207)) (n := 12)
    (lo := (441051807 / 1000000000)) (hi := (13782869 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1647) = 1/(1647 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-13782869 / 31250000) (-441051807 / 1000000000) (Real.log (1647 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (152289759 / 500000000) ≤ -Real.log (5120 / 6943) ∧
    -Real.log (5120 / 6943) ≤ (304579519 / 1000000000) := by
  have h := checkLog_sound (w := (1823 / 12063)) (n := 12)
    (lo := (152289759 / 500000000)) (hi := (304579519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6943 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6943 / 5120) = 1/(5120 / 6943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (152289759 / 500000000) (304579519 / 1000000000) (Real.log (6943 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6943 / 5120) = -Real.log (5120 / 6943) := by
    rw [show ((6943 / 5120) : ℝ) = ((5120 / 6943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (220070737 / 500000000) ≤ -Real.log (3297 / 5120) ∧
    -Real.log (3297 / 5120) ≤ (17605659 / 40000000) := by
  have h := checkLog_sound (w := (1823 / 8417)) (n := 12)
    (lo := (220070737 / 500000000)) (hi := (17605659 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3297) = 1/(3297 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-17605659 / 40000000) (-220070737 / 500000000) (Real.log (3297 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45135747 / 200000000) ≤ -Real.log (1000000 / 1253173) ∧
    -Real.log (1000000 / 1253173) ≤ (14104921 / 62500000) := by
  have h := checkLog_sound (w := (253173 / 2253173)) (n := 12)
    (lo := (45135747 / 200000000)) (hi := (14104921 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253173 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253173 / 1000000) = 1/(1000000 / 1253173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45135747 / 200000000) (14104921 / 62500000) (Real.log (1253173 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1253173 / 1000000) = -Real.log (1000000 / 1253173) := by
    rw [show ((1253173 / 1000000) : ℝ) = ((1000000 / 1253173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (291921713 / 1000000000) ≤ -Real.log (746827 / 1000000) ∧
    -Real.log (746827 / 1000000) ≤ (145960857 / 500000000) := by
  have h := checkLog_sound (w := (253173 / 1746827)) (n := 12)
    (lo := (291921713 / 1000000000)) (hi := (145960857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 746827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 746827) = 1/(746827 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-145960857 / 500000000) (-291921713 / 1000000000) (Real.log (746827 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (226016221 / 1000000000) ≤ -Real.log (250000 / 313399) ∧
    -Real.log (250000 / 313399) ≤ (113008111 / 500000000) := by
  have h := checkLog_sound (w := (63399 / 563399)) (n := 12)
    (lo := (226016221 / 1000000000)) (hi := (113008111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313399 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313399 / 250000) = 1/(250000 / 313399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (226016221 / 1000000000) (113008111 / 500000000) (Real.log (313399 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (313399 / 250000) = -Real.log (250000 / 313399) := by
    rw [show ((313399 / 250000) : ℝ) = ((250000 / 313399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (29248827 / 100000000) ≤ -Real.log (186601 / 250000) ∧
    -Real.log (186601 / 250000) ≤ (292488271 / 1000000000) := by
  have h := checkLog_sound (w := (63399 / 436601)) (n := 12)
    (lo := (29248827 / 100000000)) (hi := (292488271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 186601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 186601) = 1/(186601 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-292488271 / 1000000000) (-29248827 / 100000000) (Real.log (186601 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (167424477 / 1000000000) ≤ -Real.log (62500 / 73891) ∧
    -Real.log (62500 / 73891) ≤ (83712239 / 500000000) := by
  have h := checkLog_sound (w := (11391 / 136391)) (n := 12)
    (lo := (167424477 / 1000000000)) (hi := (83712239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73891 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73891 / 62500) = 1/(62500 / 73891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (167424477 / 1000000000) (83712239 / 500000000) (Real.log (73891 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (73891 / 62500) = -Real.log (62500 / 73891) := by
    rw [show ((73891 / 62500) : ℝ) = ((62500 / 73891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (201205949 / 1000000000) ≤ -Real.log (51109 / 62500) ∧
    -Real.log (51109 / 62500) ≤ (4024119 / 20000000) := by
  have h := checkLog_sound (w := (11391 / 113609)) (n := 12)
    (lo := (201205949 / 1000000000)) (hi := (4024119 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 51109) = 1/(51109 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4024119 / 20000000) (-201205949 / 1000000000) (Real.log (51109 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (167691727 / 1000000000) ≤ -Real.log (250000 / 295643) ∧
    -Real.log (250000 / 295643) ≤ (10480733 / 62500000) := by
  have h := checkLog_sound (w := (45643 / 545643)) (n := 12)
    (lo := (167691727 / 1000000000)) (hi := (10480733 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295643 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295643 / 250000) = 1/(250000 / 295643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (167691727 / 1000000000) (10480733 / 62500000) (Real.log (295643 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (295643 / 250000) = -Real.log (250000 / 295643) := by
    rw [show ((295643 / 250000) : ℝ) = ((250000 / 295643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (201592453 / 1000000000) ≤ -Real.log (204357 / 250000) ∧
    -Real.log (204357 / 250000) ≤ (100796227 / 500000000) := by
  have h := checkLog_sound (w := (45643 / 454357)) (n := 12)
    (lo := (201592453 / 1000000000)) (hi := (100796227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 204357) = 1/(204357 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-100796227 / 500000000) (-201592453 / 1000000000) (Real.log (204357 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (744720993 / 1000000000) ≤ -Real.log (100000000000 / 210585380649) ∧
    -Real.log (100000000000 / 210585380649) ≤ (148944199 / 200000000) := by
  have h := checkLog_sound (w := (10585380649 / 410585380649)) (n := 12)
    (lo := (51573813 / 1000000000)) (hi := (25786907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210585380649 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(210585380649 / 200000000000) = 1/(100000000000 / 210585380649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (744720993 / 1000000000) (148944199 / 200000000) (Real.log (210585380649 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (210585380649 / 100000000000) = -Real.log (100000000000 / 210585380649) := by
    rw [show ((210585380649 / 100000000000) : ℝ) = ((100000000000 / 210585380649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (373031661 / 500000000) ≤ -Real.log (500000000000 / 1054341226473) ∧
    -Real.log (500000000000 / 1054341226473) ≤ (186515831 / 250000000) := by
  have h := checkLog_sound (w := (54341226473 / 2054341226473)) (n := 12)
    (lo := (26458071 / 500000000)) (hi := (52916143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1054341226473 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1054341226473 / 1000000000000) = 1/(500000000000 / 1054341226473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (373031661 / 500000000) (186515831 / 250000000) (Real.log (1054341226473 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1054341226473 / 500000000000) = -Real.log (500000000000 / 1054341226473) := by
    rw [show ((1054341226473 / 500000000000) : ℝ) = ((500000000000 / 1054341226473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (8087507 / 15625000) ≤ -Real.log (100000000000 / 167799637667) ∧
    -Real.log (100000000000 / 167799637667) ≤ (517600449 / 1000000000) := by
  have h := checkLog_sound (w := (67799637667 / 267799637667)) (n := 12)
    (lo := (8087507 / 15625000)) (hi := (517600449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167799637667 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167799637667 / 100000000000) = 1/(100000000000 / 167799637667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (8087507 / 15625000) (517600449 / 1000000000) (Real.log (167799637667 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (167799637667 / 100000000000) = -Real.log (100000000000 / 167799637667) := by
    rw [show ((167799637667 / 100000000000) : ℝ) = ((100000000000 / 167799637667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (518504491 / 1000000000) ≤ -Real.log (500000000000 / 839757021667) ∧
    -Real.log (500000000000 / 839757021667) ≤ (129626123 / 250000000) := by
  have h := checkLog_sound (w := (339757021667 / 1339757021667)) (n := 12)
    (lo := (518504491 / 1000000000)) (hi := (129626123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839757021667 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839757021667 / 500000000000) = 1/(500000000000 / 839757021667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (518504491 / 1000000000) (129626123 / 250000000) (Real.log (839757021667 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (839757021667 / 500000000000) = -Real.log (500000000000 / 839757021667) := by
    rw [show ((839757021667 / 500000000000) : ℝ) = ((500000000000 / 839757021667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (368630427 / 1000000000) ≤ -Real.log (125000000000 / 180719149269) ∧
    -Real.log (125000000000 / 180719149269) ≤ (92157607 / 250000000) := by
  have h := checkLog_sound (w := (55719149269 / 305719149269)) (n := 12)
    (lo := (368630427 / 1000000000)) (hi := (92157607 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180719149269 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180719149269 / 125000000000) = 1/(125000000000 / 180719149269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (368630427 / 1000000000) (92157607 / 250000000) (Real.log (180719149269 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (180719149269 / 125000000000) = -Real.log (125000000000 / 180719149269) := by
    rw [show ((180719149269 / 125000000000) : ℝ) = ((125000000000 / 180719149269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (18464209 / 50000000) ≤ -Real.log (500000000000 / 723349334743) ∧
    -Real.log (500000000000 / 723349334743) ≤ (369284181 / 1000000000) := by
  have h := checkLog_sound (w := (223349334743 / 1223349334743)) (n := 12)
    (lo := (18464209 / 50000000)) (hi := (369284181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723349334743 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723349334743 / 500000000000) = 1/(500000000000 / 723349334743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (18464209 / 50000000) (369284181 / 1000000000) (Real.log (723349334743 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (723349334743 / 500000000000) = -Real.log (500000000000 / 723349334743) := by
    rw [show ((723349334743 / 500000000000) : ℝ) = ((500000000000 / 723349334743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16950363 / 500000000) ≤ -Real.log (60416716551 / 62500000000) ∧
    -Real.log (60416716551 / 62500000000) ≤ (33900727 / 1000000000) := by
  have h := checkLog_sound (w := (2083283449 / 122916716551)) (n := 12)
    (lo := (16950363 / 500000000)) (hi := (33900727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60416716551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60416716551) = 1/(60416716551 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-33900727 / 1000000000) (-16950363 / 500000000) (Real.log (60416716551 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1055671 / 31250000) ≤ -Real.log (3776495119 / 3906250000) ∧
    -Real.log (3776495119 / 3906250000) ≤ (33781473 / 1000000000) := by
  have h := checkLog_sound (w := (129754881 / 7682745119)) (n := 12)
    (lo := (1055671 / 31250000)) (hi := (33781473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3776495119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3776495119) = 1/(3776495119 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-33781473 / 1000000000) (-1055671 / 31250000) (Real.log (3776495119 / 3906250000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell181
