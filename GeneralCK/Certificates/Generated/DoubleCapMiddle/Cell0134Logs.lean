import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0134
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

theorem reflection_log_1_neg : (152217739 / 500000000) ≤ -Real.log (2560 / 3471) ∧
    -Real.log (2560 / 3471) ≤ (304435479 / 1000000000) := by
  have h := checkLog_sound (w := (911 / 6031)) (n := 12)
    (lo := (152217739 / 500000000)) (hi := (304435479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3471 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3471 / 2560) = 1/(2560 / 3471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (152217739 / 500000000) (304435479 / 1000000000) (Real.log (3471 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3471 / 2560) = -Real.log (2560 / 3471) := by
    rw [show ((3471 / 2560) : ℝ) = ((2560 / 3471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (219919107 / 500000000) ≤ -Real.log (1649 / 2560) ∧
    -Real.log (1649 / 2560) ≤ (87967643 / 200000000) := by
  have h := checkLog_sound (w := (911 / 4209)) (n := 12)
    (lo := (219919107 / 500000000)) (hi := (87967643 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1649) = 1/(1649 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-87967643 / 200000000) (-219919107 / 500000000) (Real.log (1649 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (758927 / 2500000) ≤ -Real.log (640 / 867) ∧
    -Real.log (640 / 867) ≤ (303570801 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 1507)) (n := 12)
    (lo := (758927 / 2500000)) (hi := (303570801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((867 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(867 / 640) = 1/(640 / 867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (758927 / 2500000) (303570801 / 1000000000) (Real.log (867 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (867 / 640) = -Real.log (640 / 867) := by
    rw [show ((867 / 640) : ℝ) = ((640 / 867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (438020583 / 1000000000) ≤ -Real.log (413 / 640) ∧
    -Real.log (413 / 640) ≤ (54752573 / 125000000) := by
  have h := checkLog_sound (w := (227 / 1053)) (n := 12)
    (lo := (438020583 / 1000000000)) (hi := (54752573 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 413) = 1/(413 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-54752573 / 125000000) (-438020583 / 1000000000) (Real.log (413 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (268748991 / 500000000) ≤ -Real.log (1280 / 2191) ∧
    -Real.log (1280 / 2191) ≤ (537497983 / 1000000000) := by
  have h := checkLog_sound (w := (911 / 3471)) (n := 12)
    (lo := (268748991 / 500000000)) (hi := (537497983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2191 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2191 / 1280) = 1/(1280 / 2191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (268748991 / 500000000) (537497983 / 1000000000) (Real.log (2191 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2191 / 1280) = -Real.log (1280 / 2191) := by
    rw [show ((2191 / 1280) : ℝ) = ((1280 / 2191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (155477339 / 125000000) ≤ -Real.log (369 / 1280) ∧
    -Real.log (369 / 1280) ≤ (621909357 / 500000000) := by
  have h := checkLog_sound (w := (271 / 1009)) (n := 12)
    (lo := (137667883 / 250000000)) (hi := (550671533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 369) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 369) = 1/(369 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-621909357 / 500000000) (-155477339 / 125000000) (Real.log (369 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (268063903 / 500000000) ≤ -Real.log (320 / 547) ∧
    -Real.log (320 / 547) ≤ (536127807 / 1000000000) := by
  have h := checkLog_sound (w := (227 / 867)) (n := 12)
    (lo := (268063903 / 500000000)) (hi := (536127807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547 / 320) = 1/(320 / 547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (268063903 / 500000000) (536127807 / 1000000000) (Real.log (547 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (547 / 320) = -Real.log (320 / 547) := by
    rw [show ((547 / 320) : ℝ) = ((320 / 547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (617860751 / 500000000) ≤ -Real.log (93 / 320) ∧
    -Real.log (93 / 320) ≤ (38616297 / 31250000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 93) = 1/(93 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-38616297 / 31250000) (-617860751 / 500000000) (Real.log (93 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (207780321 / 500000000) ≤ -Real.log (50000 / 75761) ∧
    -Real.log (50000 / 75761) ≤ (415560643 / 1000000000) := by
  have h := checkLog_sound (w := (25761 / 125761)) (n := 12)
    (lo := (207780321 / 500000000)) (hi := (415560643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75761 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75761 / 50000) = 1/(50000 / 75761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (207780321 / 500000000) (415560643 / 1000000000) (Real.log (75761 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (75761 / 50000) = -Real.log (50000 / 75761) := by
    rw [show ((75761 / 50000) : ℝ) = ((50000 / 75761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (362030049 / 500000000) ≤ -Real.log (24239 / 50000) ∧
    -Real.log (24239 / 50000) ≤ (7240601 / 10000000) := by
  have h := checkLog_sound (w := (761 / 49239)) (n := 12)
    (lo := (15456459 / 500000000)) (hi := (30912919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24239) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 24239) = 1/(24239 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7240601 / 10000000) (-362030049 / 500000000) (Real.log (24239 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (83352609 / 200000000) ≤ -Real.log (1000000 / 1517043) ∧
    -Real.log (1000000 / 1517043) ≤ (208381523 / 500000000) := by
  have h := checkLog_sound (w := (517043 / 2517043)) (n := 12)
    (lo := (83352609 / 200000000)) (hi := (208381523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1517043 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1517043 / 1000000) = 1/(1000000 / 1517043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (83352609 / 200000000) (208381523 / 500000000) (Real.log (1517043 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1517043 / 1000000) = -Real.log (1000000 / 1517043) := by
    rw [show ((1517043 / 1000000) : ℝ) = ((1000000 / 1517043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (145565531 / 200000000) ≤ -Real.log (482957 / 1000000) ∧
    -Real.log (482957 / 1000000) ≤ (727827657 / 1000000000) := by
  have h := checkLog_sound (w := (17043 / 982957)) (n := 12)
    (lo := (1387219 / 40000000)) (hi := (8670119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 482957) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 482957) = 1/(482957 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-727827657 / 1000000000) (-145565531 / 200000000) (Real.log (482957 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (331517123 / 1000000000) ≤ -Real.log (25000 / 34827) ∧
    -Real.log (25000 / 34827) ≤ (82879281 / 250000000) := by
  have h := checkLog_sound (w := (9827 / 59827)) (n := 12)
    (lo := (331517123 / 1000000000)) (hi := (82879281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34827 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34827 / 25000) = 1/(25000 / 34827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (331517123 / 1000000000) (82879281 / 250000000) (Real.log (34827 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (34827 / 25000) = -Real.log (25000 / 34827) := by
    rw [show ((34827 / 25000) : ℝ) = ((25000 / 34827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (124839573 / 250000000) ≤ -Real.log (15173 / 25000) ∧
    -Real.log (15173 / 25000) ≤ (499358293 / 1000000000) := by
  have h := checkLog_sound (w := (9827 / 40173)) (n := 12)
    (lo := (124839573 / 250000000)) (hi := (499358293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 15173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 15173) = 1/(15173 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-499358293 / 1000000000) (-124839573 / 250000000) (Real.log (15173 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (66534577 / 200000000) ≤ -Real.log (1000000 / 1394691) ∧
    -Real.log (1000000 / 1394691) ≤ (166336443 / 500000000) := by
  have h := checkLog_sound (w := (394691 / 2394691)) (n := 12)
    (lo := (66534577 / 200000000)) (hi := (166336443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1394691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1394691 / 1000000) = 1/(1000000 / 1394691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (66534577 / 200000000) (166336443 / 500000000) (Real.log (1394691 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1394691 / 1000000) = -Real.log (1000000 / 1394691) := by
    rw [show ((1394691 / 1000000) : ℝ) = ((1000000 / 1394691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (502016207 / 1000000000) ≤ -Real.log (605309 / 1000000) ∧
    -Real.log (605309 / 1000000) ≤ (31376013 / 62500000) := by
  have h := checkLog_sound (w := (394691 / 1605309)) (n := 12)
    (lo := (502016207 / 1000000000)) (hi := (31376013 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 605309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 605309) = 1/(605309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-31376013 / 62500000) (-502016207 / 1000000000) (Real.log (605309 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1139620741 / 1000000000) ≤ -Real.log (1562500000 / 4883723029) ∧
    -Real.log (1562500000 / 4883723029) ≤ (1139620743 / 1000000000) := by
  have h := checkLog_sound (w := (1758723029 / 8008723029)) (n := 12)
    (lo := (446473561 / 1000000000)) (hi := (223236781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4883723029 / 3125000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4883723029 / 3125000000) = 1/(1562500000 / 4883723029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1139620741 / 1000000000) (1139620743 / 1000000000) (Real.log (4883723029 / 1562500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4883723029 / 1562500000) = -Real.log (1562500000 / 4883723029) := by
    rw [show ((4883723029 / 1562500000) : ℝ) = ((1562500000 / 4883723029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1144590701 / 1000000000) ≤ -Real.log (31250000000 / 98161106993) ∧
    -Real.log (31250000000 / 98161106993) ≤ (1144590703 / 1000000000) := by
  have h := checkLog_sound (w := (35661106993 / 160661106993)) (n := 12)
    (lo := (451443521 / 1000000000)) (hi := (225721761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98161106993 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(98161106993 / 62500000000) = 1/(31250000000 / 98161106993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1144590701 / 1000000000) (1144590703 / 1000000000) (Real.log (98161106993 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (98161106993 / 31250000000) = -Real.log (31250000000 / 98161106993) := by
    rw [show ((98161106993 / 31250000000) : ℝ) = ((31250000000 / 98161106993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (415437707 / 500000000) ≤ -Real.log (125000000000 / 286915903249) ∧
    -Real.log (125000000000 / 286915903249) ≤ (103859427 / 125000000) := by
  have h := checkLog_sound (w := (36915903249 / 536915903249)) (n := 12)
    (lo := (68864117 / 500000000)) (hi := (27545647 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286915903249 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(286915903249 / 250000000000) = 1/(125000000000 / 286915903249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (415437707 / 500000000) (103859427 / 125000000) (Real.log (286915903249 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (286915903249 / 125000000000) = -Real.log (125000000000 / 286915903249) := by
    rw [show ((286915903249 / 125000000000) : ℝ) = ((125000000000 / 286915903249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (208672273 / 250000000) ≤ -Real.log (100000000000 / 230409757661) ∧
    -Real.log (100000000000 / 230409757661) ≤ (417344547 / 500000000) := by
  have h := checkLog_sound (w := (30409757661 / 430409757661)) (n := 12)
    (lo := (17692739 / 125000000)) (hi := (141541913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230409757661 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(230409757661 / 200000000000) = 1/(100000000000 / 230409757661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (208672273 / 250000000) (417344547 / 500000000) (Real.log (230409757661 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (230409757661 / 100000000000) = -Real.log (100000000000 / 230409757661) := by
    rw [show ((230409757661 / 100000000000) : ℝ) = ((100000000000 / 230409757661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0134
