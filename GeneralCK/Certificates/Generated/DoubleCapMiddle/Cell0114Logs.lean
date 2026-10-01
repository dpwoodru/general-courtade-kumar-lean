import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0114
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

theorem reflection_log_1_neg : (160786929 / 500000000) ≤ -Real.log (2560 / 3531) ∧
    -Real.log (2560 / 3531) ≤ (321573859 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 6091)) (n := 12)
    (lo := (160786929 / 500000000)) (hi := (321573859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3531 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3531 / 2560) = 1/(2560 / 3531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (160786929 / 500000000) (321573859 / 1000000000) (Real.log (3531 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3531 / 2560) = -Real.log (2560 / 3531) := by
    rw [show ((3531 / 2560) : ℝ) = ((2560 / 3531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (47690237 / 100000000) ≤ -Real.log (1589 / 2560) ∧
    -Real.log (1589 / 2560) ≤ (476902371 / 1000000000) := by
  have h := checkLog_sound (w := (971 / 4149)) (n := 12)
    (lo := (47690237 / 100000000)) (hi := (476902371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1589) = 1/(1589 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-476902371 / 1000000000) (-47690237 / 100000000) (Real.log (1589 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (320723879 / 1000000000) ≤ -Real.log (320 / 441) ∧
    -Real.log (320 / 441) ≤ (8018097 / 25000000) := by
  have h := checkLog_sound (w := (121 / 761)) (n := 12)
    (lo := (320723879 / 1000000000)) (hi := (8018097 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441 / 320) = 1/(320 / 441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (320723879 / 1000000000) (8018097 / 25000000) (Real.log (441 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (441 / 320) = -Real.log (320 / 441) := by
    rw [show ((441 / 320) : ℝ) = ((320 / 441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (475016171 / 1000000000) ≤ -Real.log (199 / 320) ∧
    -Real.log (199 / 320) ≤ (118754043 / 250000000) := by
  have h := checkLog_sound (w := (121 / 519)) (n := 12)
    (lo := (475016171 / 1000000000)) (hi := (118754043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 199) = 1/(199 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-118754043 / 250000000) (-475016171 / 1000000000) (Real.log (199 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (564514483 / 1000000000) ≤ -Real.log (1280 / 2251) ∧
    -Real.log (1280 / 2251) ≤ (141128621 / 250000000) := by
  have h := checkLog_sound (w := (971 / 3531)) (n := 12)
    (lo := (564514483 / 1000000000)) (hi := (141128621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2251 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2251 / 1280) = 1/(1280 / 2251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (564514483 / 1000000000) (141128621 / 250000000) (Real.log (2251 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2251 / 1280) = -Real.log (1280 / 2251) := by
    rw [show ((2251 / 1280) : ℝ) = ((1280 / 2251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (710637039 / 500000000) ≤ -Real.log (309 / 1280) ∧
    -Real.log (309 / 1280) ≤ (1421274081 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 629)) (n := 12)
    (lo := (17489859 / 500000000)) (hi := (34979719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 309) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 309) = 1/(309 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1421274081 / 1000000000) (-710637039 / 500000000) (Real.log (309 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (281590427 / 500000000) ≤ -Real.log (160 / 281) ∧
    -Real.log (160 / 281) ≤ (112636171 / 200000000) := by
  have h := checkLog_sound (w := (121 / 441)) (n := 12)
    (lo := (281590427 / 500000000)) (hi := (112636171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(281 / 160) = 1/(160 / 281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (281590427 / 500000000) (112636171 / 200000000) (Real.log (281 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (281 / 160) = -Real.log (160 / 281) := by
    rw [show ((281 / 160) : ℝ) = ((160 / 281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1411612167 / 1000000000) ≤ -Real.log (39 / 160) ∧
    -Real.log (39 / 160) ≤ (141161217 / 100000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 39) = 1/(39 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-141161217 / 100000000) (-1411612167 / 1000000000) (Real.log (39 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (54946677 / 125000000) ≤ -Real.log (200000 / 310409) ∧
    -Real.log (200000 / 310409) ≤ (439573417 / 1000000000) := by
  have h := checkLog_sound (w := (110409 / 510409)) (n := 12)
    (lo := (54946677 / 125000000)) (hi := (439573417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310409 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310409 / 200000) = 1/(200000 / 310409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (54946677 / 125000000) (439573417 / 1000000000) (Real.log (310409 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (310409 / 200000) = -Real.log (200000 / 310409) := by
    rw [show ((310409 / 200000) : ℝ) = ((200000 / 310409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (803062497 / 1000000000) ≤ -Real.log (89591 / 200000) ∧
    -Real.log (89591 / 200000) ≤ (803062499 / 1000000000) := by
  have h := checkLog_sound (w := (10409 / 189591)) (n := 12)
    (lo := (109915317 / 1000000000)) (hi := (54957659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 89591) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 89591) = 1/(89591 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-803062499 / 1000000000) (-803062497 / 1000000000) (Real.log (89591 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (88154867 / 200000000) ≤ -Real.log (100000 / 155391) ∧
    -Real.log (100000 / 155391) ≤ (6887099 / 15625000) := by
  have h := checkLog_sound (w := (55391 / 255391)) (n := 12)
    (lo := (88154867 / 200000000)) (hi := (6887099 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155391 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155391 / 100000) = 1/(100000 / 155391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (88154867 / 200000000) (6887099 / 15625000) (Real.log (155391 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (155391 / 100000) = -Real.log (100000 / 155391) := by
    rw [show ((155391 / 100000) : ℝ) = ((100000 / 155391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (807234553 / 1000000000) ≤ -Real.log (44609 / 100000) ∧
    -Real.log (44609 / 100000) ≤ (161446911 / 200000000) := by
  have h := checkLog_sound (w := (5391 / 94609)) (n := 12)
    (lo := (114087373 / 1000000000)) (hi := (57043687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44609) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 44609) = 1/(44609 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-161446911 / 200000000) (-807234553 / 1000000000) (Real.log (44609 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (88737439 / 250000000) ≤ -Real.log (1000000 / 1426109) ∧
    -Real.log (1000000 / 1426109) ≤ (354949757 / 1000000000) := by
  have h := checkLog_sound (w := (426109 / 2426109)) (n := 12)
    (lo := (88737439 / 250000000)) (hi := (354949757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1426109 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1426109 / 1000000) = 1/(1000000 / 1426109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (88737439 / 250000000) (354949757 / 1000000000) (Real.log (1426109 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1426109 / 1000000) = -Real.log (1000000 / 1426109) := by
    rw [show ((1426109 / 1000000) : ℝ) = ((1000000 / 1426109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (138828949 / 250000000) ≤ -Real.log (573891 / 1000000) ∧
    -Real.log (573891 / 1000000) ≤ (555315797 / 1000000000) := by
  have h := checkLog_sound (w := (426109 / 1573891)) (n := 12)
    (lo := (138828949 / 250000000)) (hi := (555315797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 573891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 573891) = 1/(573891 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-555315797 / 1000000000) (-138828949 / 250000000) (Real.log (573891 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (178071251 / 500000000) ≤ -Real.log (1000000 / 1427811) ∧
    -Real.log (1000000 / 1427811) ≤ (356142503 / 1000000000) := by
  have h := checkLog_sound (w := (427811 / 2427811)) (n := 12)
    (lo := (178071251 / 500000000)) (hi := (356142503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1427811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1427811 / 1000000) = 1/(1000000 / 1427811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (178071251 / 500000000) (356142503 / 1000000000) (Real.log (1427811 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1427811 / 1000000) = -Real.log (1000000 / 1427811) := by
    rw [show ((1427811 / 1000000) : ℝ) = ((1000000 / 1427811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (279142961 / 500000000) ≤ -Real.log (572189 / 1000000) ∧
    -Real.log (572189 / 1000000) ≤ (558285923 / 1000000000) := by
  have h := checkLog_sound (w := (427811 / 1572189)) (n := 12)
    (lo := (279142961 / 500000000)) (hi := (558285923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 572189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 572189) = 1/(572189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-558285923 / 1000000000) (-279142961 / 500000000) (Real.log (572189 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1242635913 / 1000000000) ≤ -Real.log (125000000000 / 433091772611) ∧
    -Real.log (125000000000 / 433091772611) ≤ (248527183 / 200000000) := by
  have h := checkLog_sound (w := (183091772611 / 683091772611)) (n := 12)
    (lo := (549488733 / 1000000000)) (hi := (274744367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433091772611 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(433091772611 / 250000000000) = 1/(125000000000 / 433091772611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1242635913 / 1000000000) (248527183 / 200000000) (Real.log (433091772611 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (433091772611 / 125000000000) = -Real.log (125000000000 / 433091772611) := by
    rw [show ((433091772611 / 125000000000) : ℝ) = ((125000000000 / 433091772611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (156001111 / 125000000) ≤ -Real.log (6250000000 / 21771251317) ∧
    -Real.log (6250000000 / 21771251317) ≤ (124800889 / 100000000) := by
  have h := checkLog_sound (w := (9271251317 / 34271251317)) (n := 12)
    (lo := (138715427 / 250000000)) (hi := (554861709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21771251317 / 12500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(21771251317 / 12500000000) = 1/(6250000000 / 21771251317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (156001111 / 125000000) (124800889 / 100000000) (Real.log (21771251317 / 6250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (21771251317 / 6250000000) = -Real.log (6250000000 / 21771251317) := by
    rw [show ((21771251317 / 6250000000) : ℝ) = ((6250000000 / 21771251317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (56891597 / 62500000) ≤ -Real.log (20000000000 / 49699646797) ∧
    -Real.log (20000000000 / 49699646797) ≤ (455132777 / 500000000) := by
  have h := checkLog_sound (w := (9699646797 / 89699646797)) (n := 12)
    (lo := (54279593 / 250000000)) (hi := (217118373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49699646797 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(49699646797 / 40000000000) = 1/(20000000000 / 49699646797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (56891597 / 62500000) (455132777 / 500000000) (Real.log (49699646797 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (49699646797 / 20000000000) = -Real.log (20000000000 / 49699646797) := by
    rw [show ((49699646797 / 20000000000) : ℝ) = ((20000000000 / 49699646797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (114303553 / 125000000) ≤ -Real.log (500000000000 / 1247674282449) ∧
    -Real.log (500000000000 / 1247674282449) ≤ (457214213 / 500000000) := by
  have h := checkLog_sound (w := (247674282449 / 2247674282449)) (n := 12)
    (lo := (55320311 / 250000000)) (hi := (44256249 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247674282449 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1247674282449 / 1000000000000) = 1/(500000000000 / 1247674282449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (114303553 / 125000000) (457214213 / 500000000) (Real.log (1247674282449 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1247674282449 / 500000000000) = -Real.log (500000000000 / 1247674282449) := by
    rw [show ((1247674282449 / 500000000000) : ℝ) = ((500000000000 / 1247674282449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0114
