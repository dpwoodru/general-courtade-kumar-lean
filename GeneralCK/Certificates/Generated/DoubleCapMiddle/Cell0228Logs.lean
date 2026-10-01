import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0228
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

theorem reflection_log_1_neg : (50601141 / 200000000) ≤ -Real.log (2560 / 3297) ∧
    -Real.log (2560 / 3297) ≤ (126502853 / 500000000) := by
  have h := checkLog_sound (w := (737 / 5857)) (n := 12)
    (lo := (50601141 / 200000000)) (hi := (126502853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3297 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3297 / 2560) = 1/(2560 / 3297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (50601141 / 200000000) (126502853 / 500000000) (Real.log (3297 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3297 / 2560) = -Real.log (2560 / 3297) := by
    rw [show ((3297 / 2560) : ℝ) = ((2560 / 3297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (169761881 / 500000000) ≤ -Real.log (1823 / 2560) ∧
    -Real.log (1823 / 2560) ≤ (339523763 / 1000000000) := by
  have h := checkLog_sound (w := (737 / 4383)) (n := 12)
    (lo := (169761881 / 500000000)) (hi := (339523763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1823) = 1/(1823 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-339523763 / 1000000000) (-169761881 / 500000000) (Real.log (1823 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (252550643 / 1000000000) ≤ -Real.log (5120 / 6591) ∧
    -Real.log (5120 / 6591) ≤ (63137661 / 250000000) := by
  have h := checkLog_sound (w := (1471 / 11711)) (n := 12)
    (lo := (252550643 / 1000000000)) (hi := (63137661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6591 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6591 / 5120) = 1/(5120 / 6591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (252550643 / 1000000000) (63137661 / 250000000) (Real.log (6591 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6591 / 5120) = -Real.log (5120 / 6591) := by
    rw [show ((6591 / 5120) : ℝ) = ((5120 / 6591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (338701281 / 1000000000) ≤ -Real.log (3649 / 5120) ∧
    -Real.log (3649 / 5120) ≤ (169350641 / 500000000) := by
  have h := checkLog_sound (w := (1471 / 8769)) (n := 12)
    (lo := (338701281 / 1000000000)) (hi := (169350641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3649) = 1/(3649 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-169350641 / 500000000) (-338701281 / 1000000000) (Real.log (3649 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (454751181 / 1000000000) ≤ -Real.log (1280 / 2017) ∧
    -Real.log (1280 / 2017) ≤ (227375591 / 500000000) := by
  have h := checkLog_sound (w := (737 / 3297)) (n := 12)
    (lo := (454751181 / 1000000000)) (hi := (227375591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2017 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2017 / 1280) = 1/(1280 / 2017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (454751181 / 1000000000) (227375591 / 500000000) (Real.log (2017 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2017 / 1280) = -Real.log (1280 / 2017) := by
    rw [show ((2017 / 1280) : ℝ) = ((1280 / 2017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (214376509 / 250000000) ≤ -Real.log (543 / 1280) ∧
    -Real.log (543 / 1280) ≤ (428753019 / 500000000) := by
  have h := checkLog_sound (w := (97 / 1183)) (n := 12)
    (lo := (20544857 / 125000000)) (hi := (164358857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 543) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 543) = 1/(543 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-428753019 / 500000000) (-214376509 / 250000000) (Real.log (543 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (18160289 / 40000000) ≤ -Real.log (2560 / 4031) ∧
    -Real.log (2560 / 4031) ≤ (227003613 / 500000000) := by
  have h := checkLog_sound (w := (1471 / 6591)) (n := 12)
    (lo := (18160289 / 40000000)) (hi := (227003613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4031 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4031 / 2560) = 1/(2560 / 4031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (18160289 / 40000000) (227003613 / 500000000) (Real.log (4031 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4031 / 2560) = -Real.log (2560 / 4031) := by
    rw [show ((4031 / 2560) : ℝ) = ((2560 / 4031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (854747413 / 1000000000) ≤ -Real.log (1089 / 2560) ∧
    -Real.log (1089 / 2560) ≤ (170949483 / 200000000) := by
  have h := checkLog_sound (w := (191 / 2369)) (n := 12)
    (lo := (161600233 / 1000000000)) (hi := (80800117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1089) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1089) = 1/(1089 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-170949483 / 200000000) (-854747413 / 1000000000) (Real.log (1089 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (345600447 / 1000000000) ≤ -Real.log (500000 / 706419) ∧
    -Real.log (500000 / 706419) ≤ (5400007 / 15625000) := by
  have h := checkLog_sound (w := (206419 / 1206419)) (n := 12)
    (lo := (345600447 / 1000000000)) (hi := (5400007 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((706419 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(706419 / 500000) = 1/(500000 / 706419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (345600447 / 1000000000) (5400007 / 15625000) (Real.log (706419 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (706419 / 500000) = -Real.log (500000 / 706419) := by
    rw [show ((706419 / 500000) : ℝ) = ((500000 / 706419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (532454517 / 1000000000) ≤ -Real.log (293581 / 500000) ∧
    -Real.log (293581 / 500000) ≤ (266227259 / 500000000) := by
  have h := checkLog_sound (w := (206419 / 793581)) (n := 12)
    (lo := (532454517 / 1000000000)) (hi := (266227259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 293581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 293581) = 1/(293581 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-266227259 / 500000000) (-532454517 / 1000000000) (Real.log (293581 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (43277447 / 125000000) ≤ -Real.log (1000000 / 1413713) ∧
    -Real.log (1000000 / 1413713) ≤ (346219577 / 1000000000) := by
  have h := checkLog_sound (w := (413713 / 2413713)) (n := 12)
    (lo := (43277447 / 125000000)) (hi := (346219577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1413713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1413713 / 1000000) = 1/(1000000 / 1413713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (43277447 / 125000000) (346219577 / 1000000000) (Real.log (1413713 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1413713 / 1000000) = -Real.log (1000000 / 1413713) := by
    rw [show ((1413713 / 1000000) : ℝ) = ((1000000 / 1413713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (66743231 / 125000000) ≤ -Real.log (586287 / 1000000) ∧
    -Real.log (586287 / 1000000) ≤ (533945849 / 1000000000) := by
  have h := checkLog_sound (w := (413713 / 1586287)) (n := 12)
    (lo := (66743231 / 125000000)) (hi := (533945849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 586287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 586287) = 1/(586287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-533945849 / 1000000000) (-66743231 / 125000000) (Real.log (586287 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (267238519 / 1000000000) ≤ -Real.log (62500 / 81647) ∧
    -Real.log (62500 / 81647) ≤ (6680963 / 25000000) := by
  have h := checkLog_sound (w := (19147 / 144147)) (n := 12)
    (lo := (267238519 / 1000000000)) (hi := (6680963 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81647 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81647 / 62500) = 1/(62500 / 81647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (267238519 / 1000000000) (6680963 / 25000000) (Real.log (81647 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (81647 / 62500) = -Real.log (62500 / 81647) := by
    rw [show ((81647 / 62500) : ℝ) = ((62500 / 81647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (365790651 / 1000000000) ≤ -Real.log (43353 / 62500) ∧
    -Real.log (43353 / 62500) ≤ (91447663 / 250000000) := by
  have h := checkLog_sound (w := (19147 / 105853)) (n := 12)
    (lo := (365790651 / 1000000000)) (hi := (91447663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 43353) = 1/(43353 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-91447663 / 250000000) (-365790651 / 1000000000) (Real.log (43353 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (53556833 / 200000000) ≤ -Real.log (200000 / 261413) ∧
    -Real.log (200000 / 261413) ≤ (133892083 / 500000000) := by
  have h := checkLog_sound (w := (61413 / 461413)) (n := 12)
    (lo := (53556833 / 200000000)) (hi := (133892083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261413 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(261413 / 200000) = 1/(200000 / 261413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (53556833 / 200000000) (133892083 / 500000000) (Real.log (261413 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (261413 / 200000) = -Real.log (200000 / 261413) := by
    rw [show ((261413 / 200000) : ℝ) = ((200000 / 261413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (366819079 / 1000000000) ≤ -Real.log (138587 / 200000) ∧
    -Real.log (138587 / 200000) ≤ (9170477 / 25000000) := by
  have h := checkLog_sound (w := (61413 / 338587)) (n := 12)
    (lo := (366819079 / 1000000000)) (hi := (9170477 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 138587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 138587) = 1/(138587 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-9170477 / 25000000) (-366819079 / 1000000000) (Real.log (138587 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (219513741 / 250000000) ≤ -Real.log (250000000000 / 601553744963) ∧
    -Real.log (250000000000 / 601553744963) ≤ (439027483 / 500000000) := by
  have h := checkLog_sound (w := (101553744963 / 1101553744963)) (n := 12)
    (lo := (23113473 / 125000000)) (hi := (36981557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601553744963 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(601553744963 / 500000000000) = 1/(250000000000 / 601553744963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (219513741 / 250000000) (439027483 / 500000000) (Real.log (601553744963 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (601553744963 / 250000000000) = -Real.log (250000000000 / 601553744963) := by
    rw [show ((601553744963 / 250000000000) : ℝ) = ((250000000000 / 601553744963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (55010339 / 62500000) ≤ -Real.log (62500000000 / 150706160123) ∧
    -Real.log (62500000000 / 150706160123) ≤ (440082713 / 500000000) := by
  have h := checkLog_sound (w := (25706160123 / 275706160123)) (n := 12)
    (lo := (46754561 / 250000000)) (hi := (37403649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150706160123 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(150706160123 / 125000000000) = 1/(62500000000 / 150706160123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (55010339 / 62500000) (440082713 / 500000000) (Real.log (150706160123 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (150706160123 / 62500000000) = -Real.log (62500000000 / 150706160123) := by
    rw [show ((150706160123 / 62500000000) : ℝ) = ((62500000000 / 150706160123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (633029171 / 1000000000) ≤ -Real.log (100000000000 / 188330680691) ∧
    -Real.log (100000000000 / 188330680691) ≤ (158257293 / 250000000) := by
  have h := checkLog_sound (w := (88330680691 / 288330680691)) (n := 12)
    (lo := (633029171 / 1000000000)) (hi := (158257293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188330680691 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188330680691 / 100000000000) = 1/(100000000000 / 188330680691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (633029171 / 1000000000) (158257293 / 250000000) (Real.log (188330680691 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (188330680691 / 100000000000) = -Real.log (100000000000 / 188330680691) := by
    rw [show ((188330680691 / 100000000000) : ℝ) = ((100000000000 / 188330680691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (158650811 / 250000000) ≤ -Real.log (250000000000 / 471568401077) ∧
    -Real.log (250000000000 / 471568401077) ≤ (126920649 / 200000000) := by
  have h := checkLog_sound (w := (221568401077 / 721568401077)) (n := 12)
    (lo := (158650811 / 250000000)) (hi := (126920649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471568401077 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471568401077 / 250000000000) = 1/(250000000000 / 471568401077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (158650811 / 250000000) (126920649 / 200000000) (Real.log (471568401077 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (471568401077 / 250000000000) = -Real.log (250000000000 / 471568401077) := by
    rw [show ((471568401077 / 250000000000) : ℝ) = ((250000000000 / 471568401077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0228
