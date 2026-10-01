import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0209
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

theorem reflection_log_1_neg : (13080639 / 50000000) ≤ -Real.log (5120 / 6651) ∧
    -Real.log (5120 / 6651) ≤ (261612781 / 1000000000) := by
  have h := checkLog_sound (w := (1531 / 11771)) (n := 12)
    (lo := (13080639 / 50000000)) (hi := (261612781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6651 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6651 / 5120) = 1/(5120 / 6651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13080639 / 50000000) (261612781 / 1000000000) (Real.log (6651 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6651 / 5120) = -Real.log (5120 / 6651) := by
    rw [show ((6651 / 5120) : ℝ) = ((5120 / 6651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (177640413 / 500000000) ≤ -Real.log (3589 / 5120) ∧
    -Real.log (3589 / 5120) ≤ (355280827 / 1000000000) := by
  have h := checkLog_sound (w := (1531 / 8709)) (n := 12)
    (lo := (177640413 / 500000000)) (hi := (355280827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3589) = 1/(3589 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-355280827 / 1000000000) (-177640413 / 500000000) (Real.log (3589 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (130580809 / 500000000) ≤ -Real.log (640 / 831) ∧
    -Real.log (640 / 831) ≤ (261161619 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 1471)) (n := 12)
    (lo := (130580809 / 500000000)) (hi := (261161619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831 / 640) = 1/(640 / 831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (130580809 / 500000000) (261161619 / 1000000000) (Real.log (831 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (831 / 640) = -Real.log (640 / 831) := by
    rw [show ((831 / 640) : ℝ) = ((640 / 831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (44305661 / 125000000) ≤ -Real.log (449 / 640) ∧
    -Real.log (449 / 640) ≤ (354445289 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 1089)) (n := 12)
    (lo := (44305661 / 125000000)) (hi := (354445289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 449) = 1/(449 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-354445289 / 1000000000) (-44305661 / 125000000) (Real.log (449 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23439109 / 50000000) ≤ -Real.log (2560 / 4091) ∧
    -Real.log (2560 / 4091) ≤ (468782181 / 1000000000) := by
  have h := checkLog_sound (w := (1531 / 6651)) (n := 12)
    (lo := (23439109 / 50000000)) (hi := (468782181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4091 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4091 / 2560) = 1/(2560 / 4091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23439109 / 50000000) (468782181 / 1000000000) (Real.log (4091 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4091 / 2560) = -Real.log (2560 / 4091) := by
    rw [show ((4091 / 2560) : ℝ) = ((2560 / 4091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (911419801 / 1000000000) ≤ -Real.log (1029 / 2560) ∧
    -Real.log (1029 / 2560) ≤ (911419803 / 1000000000) := by
  have h := checkLog_sound (w := (251 / 2309)) (n := 12)
    (lo := (218272621 / 1000000000)) (hi := (109136311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1029) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1029) = 1/(1029 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-911419803 / 1000000000) (-911419801 / 1000000000) (Real.log (1029 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (234024297 / 500000000) ≤ -Real.log (320 / 511) ∧
    -Real.log (320 / 511) ≤ (93609719 / 200000000) := by
  have h := checkLog_sound (w := (191 / 831)) (n := 12)
    (lo := (234024297 / 500000000)) (hi := (93609719 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((511 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(511 / 320) = 1/(320 / 511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (234024297 / 500000000) (93609719 / 200000000) (Real.log (511 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (511 / 320) = -Real.log (320 / 511) := by
    rw [show ((511 / 320) : ℝ) = ((320 / 511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (90850859 / 100000000) ≤ -Real.log (129 / 320) ∧
    -Real.log (129 / 320) ≤ (56781787 / 62500000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 129) = 1/(129 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-56781787 / 62500000) (-90850859 / 100000000) (Real.log (129 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (357308643 / 1000000000) ≤ -Real.log (1000000 / 1429477) ∧
    -Real.log (1000000 / 1429477) ≤ (89327161 / 250000000) := by
  have h := checkLog_sound (w := (429477 / 2429477)) (n := 12)
    (lo := (357308643 / 1000000000)) (hi := (89327161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1429477 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1429477 / 1000000) = 1/(1000000 / 1429477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (357308643 / 1000000000) (89327161 / 250000000) (Real.log (1429477 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1429477 / 1000000) = -Real.log (1000000 / 1429477) := by
    rw [show ((1429477 / 1000000) : ℝ) = ((1000000 / 1429477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (280600897 / 500000000) ≤ -Real.log (570523 / 1000000) ∧
    -Real.log (570523 / 1000000) ≤ (112240359 / 200000000) := by
  have h := checkLog_sound (w := (429477 / 1570523)) (n := 12)
    (lo := (280600897 / 500000000)) (hi := (112240359 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 570523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 570523) = 1/(570523 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-112240359 / 200000000) (-280600897 / 500000000) (Real.log (570523 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (89480841 / 250000000) ≤ -Real.log (250000 / 357589) ∧
    -Real.log (250000 / 357589) ≤ (71584673 / 200000000) := by
  have h := checkLog_sound (w := (107589 / 607589)) (n := 12)
    (lo := (89480841 / 250000000)) (hi := (71584673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357589 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357589 / 250000) = 1/(250000 / 357589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (89480841 / 250000000) (71584673 / 200000000) (Real.log (357589 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (357589 / 250000) = -Real.log (250000 / 357589) := by
    rw [show ((357589 / 250000) : ℝ) = ((250000 / 357589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (281371837 / 500000000) ≤ -Real.log (142411 / 250000) ∧
    -Real.log (142411 / 250000) ≤ (22509747 / 40000000) := by
  have h := checkLog_sound (w := (107589 / 392411)) (n := 12)
    (lo := (281371837 / 500000000)) (hi := (22509747 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 142411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 142411) = 1/(142411 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-22509747 / 40000000) (-281371837 / 500000000) (Real.log (142411 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (277626433 / 1000000000) ≤ -Real.log (1000000 / 1319993) ∧
    -Real.log (1000000 / 1319993) ≤ (138813217 / 500000000) := by
  have h := checkLog_sound (w := (319993 / 2319993)) (n := 12)
    (lo := (277626433 / 1000000000)) (hi := (138813217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319993 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1319993 / 1000000) = 1/(1000000 / 1319993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (277626433 / 1000000000) (138813217 / 500000000) (Real.log (1319993 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1319993 / 1000000) = -Real.log (1000000 / 1319993) := by
    rw [show ((1319993 / 1000000) : ℝ) = ((1000000 / 1319993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (192826093 / 500000000) ≤ -Real.log (680007 / 1000000) ∧
    -Real.log (680007 / 1000000) ≤ (385652187 / 1000000000) := by
  have h := checkLog_sound (w := (319993 / 1680007)) (n := 12)
    (lo := (192826093 / 500000000)) (hi := (385652187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 680007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 680007) = 1/(680007 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-385652187 / 1000000000) (-192826093 / 500000000) (Real.log (680007 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (55635257 / 200000000) ≤ -Real.log (1000000 / 1320719) ∧
    -Real.log (1000000 / 1320719) ≤ (139088143 / 500000000) := by
  have h := checkLog_sound (w := (320719 / 2320719)) (n := 12)
    (lo := (55635257 / 200000000)) (hi := (139088143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1320719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1320719 / 1000000) = 1/(1000000 / 1320719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (55635257 / 200000000) (139088143 / 500000000) (Real.log (1320719 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1320719 / 1000000) = -Real.log (1000000 / 1320719) := by
    rw [show ((1320719 / 1000000) : ℝ) = ((1000000 / 1320719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (386720393 / 1000000000) ≤ -Real.log (679281 / 1000000) ∧
    -Real.log (679281 / 1000000) ≤ (193360197 / 500000000) := by
  have h := checkLog_sound (w := (320719 / 1679281)) (n := 12)
    (lo := (386720393 / 1000000000)) (hi := (193360197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 679281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 679281) = 1/(679281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-193360197 / 500000000) (-386720393 / 1000000000) (Real.log (679281 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (918510437 / 1000000000) ≤ -Real.log (500000000000 / 1252777714483) ∧
    -Real.log (500000000000 / 1252777714483) ≤ (918510439 / 1000000000) := by
  have h := checkLog_sound (w := (252777714483 / 2252777714483)) (n := 12)
    (lo := (225363257 / 1000000000)) (hi := (112681629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252777714483 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1252777714483 / 1000000000000) = 1/(500000000000 / 1252777714483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (918510437 / 1000000000) (918510439 / 1000000000) (Real.log (1252777714483 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1252777714483 / 500000000000) = -Real.log (500000000000 / 1252777714483) := by
    rw [show ((1252777714483 / 500000000000) : ℝ) = ((500000000000 / 1252777714483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (460333519 / 500000000) ≤ -Real.log (500000000000 / 1255482371447) ∧
    -Real.log (500000000000 / 1255482371447) ≤ (5754169 / 6250000) := by
  have h := checkLog_sound (w := (255482371447 / 2255482371447)) (n := 12)
    (lo := (113759929 / 500000000)) (hi := (227519859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1255482371447 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1255482371447 / 1000000000000) = 1/(500000000000 / 1255482371447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (460333519 / 500000000) (5754169 / 6250000) (Real.log (1255482371447 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1255482371447 / 500000000000) = -Real.log (500000000000 / 1255482371447) := by
    rw [show ((1255482371447 / 500000000000) : ℝ) = ((500000000000 / 1255482371447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (33163931 / 50000000) ≤ -Real.log (500000000000 / 970573097041) ∧
    -Real.log (500000000000 / 970573097041) ≤ (663278621 / 1000000000) := by
  have h := checkLog_sound (w := (470573097041 / 1470573097041)) (n := 12)
    (lo := (33163931 / 50000000)) (hi := (663278621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((970573097041 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(970573097041 / 500000000000) = 1/(500000000000 / 970573097041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (33163931 / 50000000) (663278621 / 1000000000) (Real.log (970573097041 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (970573097041 / 500000000000) = -Real.log (500000000000 / 970573097041) := by
    rw [show ((970573097041 / 500000000000) : ℝ) = ((500000000000 / 970573097041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (332448339 / 500000000) ≤ -Real.log (500000000000 / 972144811941) ∧
    -Real.log (500000000000 / 972144811941) ≤ (664896679 / 1000000000) := by
  have h := checkLog_sound (w := (472144811941 / 1472144811941)) (n := 12)
    (lo := (332448339 / 500000000)) (hi := (664896679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972144811941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972144811941 / 500000000000) = 1/(500000000000 / 972144811941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (332448339 / 500000000) (664896679 / 1000000000) (Real.log (972144811941 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (972144811941 / 500000000000) = -Real.log (500000000000 / 972144811941) := by
    rw [show ((972144811941 / 500000000000) : ℝ) = ((500000000000 / 972144811941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0209
