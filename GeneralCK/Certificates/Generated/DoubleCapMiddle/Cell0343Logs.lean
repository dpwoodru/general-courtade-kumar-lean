import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0343
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

theorem reflection_log_1_neg : (21380319 / 100000000) ≤ -Real.log (10240 / 12681) ∧
    -Real.log (10240 / 12681) ≤ (213803191 / 1000000000) := by
  have h := checkLog_sound (w := (2441 / 22921)) (n := 12)
    (lo := (21380319 / 100000000)) (hi := (213803191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12681 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12681 / 10240) = 1/(10240 / 12681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (21380319 / 100000000) (213803191 / 1000000000) (Real.log (12681 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12681 / 10240) = -Real.log (10240 / 12681) := by
    rw [show ((12681 / 10240) : ℝ) = ((10240 / 12681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (272306099 / 1000000000) ≤ -Real.log (7799 / 10240) ∧
    -Real.log (7799 / 10240) ≤ (2723061 / 10000000) := by
  have h := checkLog_sound (w := (2441 / 18039)) (n := 12)
    (lo := (272306099 / 1000000000)) (hi := (2723061 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7799) = 1/(7799 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2723061 / 10000000) (-272306099 / 1000000000) (Real.log (7799 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (53391647 / 250000000) ≤ -Real.log (5120 / 6339) ∧
    -Real.log (5120 / 6339) ≤ (213566589 / 1000000000) := by
  have h := checkLog_sound (w := (1219 / 11459)) (n := 12)
    (lo := (53391647 / 250000000)) (hi := (213566589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6339 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6339 / 5120) = 1/(5120 / 6339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (53391647 / 250000000) (213566589 / 1000000000) (Real.log (6339 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6339 / 5120) = -Real.log (5120 / 6339) := by
    rw [show ((6339 / 5120) : ℝ) = ((5120 / 6339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (67980377 / 250000000) ≤ -Real.log (3901 / 5120) ∧
    -Real.log (3901 / 5120) ≤ (271921509 / 1000000000) := by
  have h := checkLog_sound (w := (1219 / 9021)) (n := 12)
    (lo := (67980377 / 250000000)) (hi := (271921509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3901) = 1/(3901 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-271921509 / 1000000000) (-67980377 / 250000000) (Real.log (3901 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (389849017 / 1000000000) ≤ -Real.log (5120 / 7561) ∧
    -Real.log (5120 / 7561) ≤ (194924509 / 500000000) := by
  have h := checkLog_sound (w := (2441 / 12681)) (n := 12)
    (lo := (389849017 / 1000000000)) (hi := (194924509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7561 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7561 / 5120) = 1/(5120 / 7561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (389849017 / 1000000000) (194924509 / 500000000) (Real.log (7561 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7561 / 5120) = -Real.log (5120 / 7561) := by
    rw [show ((7561 / 5120) : ℝ) = ((5120 / 7561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (5060241 / 7812500) ≤ -Real.log (2679 / 5120) ∧
    -Real.log (2679 / 5120) ≤ (647710849 / 1000000000) := by
  have h := checkLog_sound (w := (2441 / 7799)) (n := 12)
    (lo := (5060241 / 7812500)) (hi := (647710849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2679) = 1/(2679 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-647710849 / 1000000000) (-5060241 / 7812500) (Real.log (2679 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (77890433 / 200000000) ≤ -Real.log (2560 / 3779) ∧
    -Real.log (2560 / 3779) ≤ (194726083 / 500000000) := by
  have h := checkLog_sound (w := (1219 / 6339)) (n := 12)
    (lo := (77890433 / 200000000)) (hi := (194726083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3779 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3779 / 2560) = 1/(2560 / 3779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (77890433 / 200000000) (194726083 / 500000000) (Real.log (3779 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3779 / 2560) = -Real.log (2560 / 3779) := by
    rw [show ((3779 / 2560) : ℝ) = ((2560 / 3779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (323295827 / 500000000) ≤ -Real.log (1341 / 2560) ∧
    -Real.log (1341 / 2560) ≤ (129318331 / 200000000) := by
  have h := checkLog_sound (w := (1219 / 3901)) (n := 12)
    (lo := (323295827 / 500000000)) (hi := (129318331 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1341) = 1/(1341 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-129318331 / 200000000) (-323295827 / 500000000) (Real.log (1341 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18302391 / 62500000) ≤ -Real.log (500000 / 670113) ∧
    -Real.log (500000 / 670113) ≤ (292838257 / 1000000000) := by
  have h := checkLog_sound (w := (170113 / 1170113)) (n := 12)
    (lo := (18302391 / 62500000)) (hi := (292838257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((670113 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(670113 / 500000) = 1/(500000 / 670113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18302391 / 62500000) (292838257 / 1000000000) (Real.log (670113 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (670113 / 500000) = -Real.log (500000 / 670113) := by
    rw [show ((670113 / 500000) : ℝ) = ((500000 / 670113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (207928963 / 500000000) ≤ -Real.log (329887 / 500000) ∧
    -Real.log (329887 / 500000) ≤ (415857927 / 1000000000) := by
  have h := checkLog_sound (w := (170113 / 829887)) (n := 12)
    (lo := (207928963 / 500000000)) (hi := (415857927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 329887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 329887) = 1/(329887 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-415857927 / 1000000000) (-207928963 / 500000000) (Real.log (329887 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (146579523 / 500000000) ≤ -Real.log (62500 / 83791) ∧
    -Real.log (62500 / 83791) ≤ (293159047 / 1000000000) := by
  have h := checkLog_sound (w := (21291 / 146291)) (n := 12)
    (lo := (146579523 / 500000000)) (hi := (293159047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83791 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83791 / 62500) = 1/(62500 / 83791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (146579523 / 500000000) (293159047 / 1000000000) (Real.log (83791 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (83791 / 62500) = -Real.log (62500 / 83791) := by
    rw [show ((83791 / 62500) : ℝ) = ((62500 / 83791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (416509877 / 1000000000) ≤ -Real.log (41209 / 62500) ∧
    -Real.log (41209 / 62500) ≤ (208254939 / 500000000) := by
  have h := checkLog_sound (w := (21291 / 103709)) (n := 12)
    (lo := (416509877 / 1000000000)) (hi := (208254939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 41209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 41209) = 1/(41209 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-208254939 / 500000000) (-416509877 / 1000000000) (Real.log (41209 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (110986633 / 500000000) ≤ -Real.log (500000 / 624269) ∧
    -Real.log (500000 / 624269) ≤ (221973267 / 1000000000) := by
  have h := checkLog_sound (w := (124269 / 1124269)) (n := 12)
    (lo := (110986633 / 500000000)) (hi := (221973267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624269 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624269 / 500000) = 1/(500000 / 624269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (110986633 / 500000000) (221973267 / 1000000000) (Real.log (624269 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (624269 / 500000) = -Real.log (500000 / 624269) := by
    rw [show ((624269 / 500000) : ℝ) = ((500000 / 624269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (71433659 / 250000000) ≤ -Real.log (375731 / 500000) ∧
    -Real.log (375731 / 500000) ≤ (285734637 / 1000000000) := by
  have h := checkLog_sound (w := (124269 / 875731)) (n := 12)
    (lo := (71433659 / 250000000)) (hi := (285734637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375731) = 1/(375731 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-285734637 / 1000000000) (-71433659 / 250000000) (Real.log (375731 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (222240743 / 1000000000) ≤ -Real.log (125000 / 156109) ∧
    -Real.log (125000 / 156109) ≤ (27780093 / 125000000) := by
  have h := checkLog_sound (w := (31109 / 281109)) (n := 12)
    (lo := (222240743 / 1000000000)) (hi := (27780093 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156109 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156109 / 125000) = 1/(125000 / 156109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (222240743 / 1000000000) (27780093 / 125000000) (Real.log (156109 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (156109 / 125000) = -Real.log (125000 / 156109) := by
    rw [show ((156109 / 125000) : ℝ) = ((125000 / 156109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (143089601 / 500000000) ≤ -Real.log (93891 / 125000) ∧
    -Real.log (93891 / 125000) ≤ (286179203 / 1000000000) := by
  have h := checkLog_sound (w := (31109 / 218891)) (n := 12)
    (lo := (143089601 / 500000000)) (hi := (286179203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 93891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 93891) = 1/(93891 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-286179203 / 1000000000) (-143089601 / 500000000) (Real.log (93891 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (354348091 / 500000000) ≤ -Real.log (12500000000 / 25391762937) ∧
    -Real.log (12500000000 / 25391762937) ≤ (88587023 / 125000000) := by
  have h := checkLog_sound (w := (391762937 / 50391762937)) (n := 12)
    (lo := (7774501 / 500000000)) (hi := (15549003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25391762937 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25391762937 / 25000000000) = 1/(12500000000 / 25391762937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (354348091 / 500000000) (88587023 / 125000000) (Real.log (25391762937 / 12500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (25391762937 / 12500000000) = -Real.log (12500000000 / 25391762937) := by
    rw [show ((25391762937 / 12500000000) : ℝ) = ((12500000000 / 25391762937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (709668923 / 1000000000) ≤ -Real.log (250000000000 / 508329491131) ∧
    -Real.log (250000000000 / 508329491131) ≤ (28386757 / 40000000) := by
  have h := checkLog_sound (w := (8329491131 / 1008329491131)) (n := 12)
    (lo := (16521743 / 1000000000)) (hi := (1032609 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((508329491131 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(508329491131 / 500000000000) = 1/(250000000000 / 508329491131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (709668923 / 1000000000) (28386757 / 40000000) (Real.log (508329491131 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (508329491131 / 250000000000) = -Real.log (250000000000 / 508329491131) := by
    rw [show ((508329491131 / 250000000000) : ℝ) = ((250000000000 / 508329491131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (507707903 / 1000000000) ≤ -Real.log (250000000000 / 415369639449) ∧
    -Real.log (250000000000 / 415369639449) ≤ (991617 / 1953125) := by
  have h := checkLog_sound (w := (165369639449 / 665369639449)) (n := 12)
    (lo := (507707903 / 1000000000)) (hi := (991617 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((415369639449 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(415369639449 / 250000000000) = 1/(250000000000 / 415369639449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (507707903 / 1000000000) (991617 / 1953125) (Real.log (415369639449 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (415369639449 / 250000000000) = -Real.log (250000000000 / 415369639449) := by
    rw [show ((415369639449 / 250000000000) : ℝ) = ((250000000000 / 415369639449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (254209973 / 500000000) ≤ -Real.log (500000000000 / 831331011493) ∧
    -Real.log (500000000000 / 831331011493) ≤ (508419947 / 1000000000) := by
  have h := checkLog_sound (w := (331331011493 / 1331331011493)) (n := 12)
    (lo := (254209973 / 500000000)) (hi := (508419947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831331011493 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831331011493 / 500000000000) = 1/(500000000000 / 831331011493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (254209973 / 500000000) (508419947 / 1000000000) (Real.log (831331011493 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (831331011493 / 500000000000) = -Real.log (500000000000 / 831331011493) := by
    rw [show ((831331011493 / 500000000000) : ℝ) = ((500000000000 / 831331011493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0343
