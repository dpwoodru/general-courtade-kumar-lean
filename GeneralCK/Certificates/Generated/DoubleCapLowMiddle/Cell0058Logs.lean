import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0058
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

theorem reflection_log_1_neg : (678306149 / 1000000000) ≤ -Real.log (102400 / 201783) ∧
    -Real.log (102400 / 201783) ≤ (13566123 / 20000000) := by
  have h := checkLog_sound (w := (99383 / 304183)) (n := 12)
    (lo := (678306149 / 1000000000)) (hi := (13566123 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201783 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201783 / 102400) = 1/(102400 / 201783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (678306149 / 1000000000) (13566123 / 20000000) (Real.log (201783 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201783 / 102400) = -Real.log (102400 / 201783) := by
    rw [show ((201783 / 102400) : ℝ) = ((102400 / 201783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3524623749 / 1000000000) ≤ -Real.log (3017 / 102400) ∧
    -Real.log (3017 / 102400) ≤ (704924751 / 200000000) := by
  have h := checkLog_sound (w := (183 / 6217)) (n := 12)
    (lo := (58887849 / 1000000000)) (hi := (1177757 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3017) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3017) = 1/(3017 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-704924751 / 200000000) (-3524623749 / 1000000000) (Real.log (3017 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (42388249 / 62500000) ≤ -Real.log (25600 / 50441) ∧
    -Real.log (25600 / 50441) ≤ (135642397 / 200000000) := by
  have h := checkLog_sound (w := (24841 / 76041)) (n := 12)
    (lo := (42388249 / 62500000)) (hi := (135642397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50441 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50441 / 25600) = 1/(25600 / 50441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (42388249 / 62500000) (135642397 / 200000000) (Real.log (50441 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50441 / 25600) = -Real.log (25600 / 50441) := by
    rw [show ((50441 / 25600) : ℝ) = ((25600 / 50441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (70366917 / 20000000) ≤ -Real.log (759 / 25600) ∧
    -Real.log (759 / 25600) ≤ (27487077 / 7812500) := by
  have h := checkLog_sound (w := (41 / 1559)) (n := 12)
    (lo := (1052199 / 20000000)) (hi := (52609951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 759) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 759) = 1/(759 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-27487077 / 7812500) (-70366917 / 20000000) (Real.log (759 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (33162077 / 50000000) ≤ -Real.log (51200 / 99383) ∧
    -Real.log (51200 / 99383) ≤ (663241541 / 1000000000) := by
  have h := checkLog_sound (w := (48183 / 150583)) (n := 12)
    (lo := (33162077 / 50000000)) (hi := (663241541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99383 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99383 / 51200) = 1/(51200 / 99383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (33162077 / 50000000) (663241541 / 1000000000) (Real.log (99383 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99383 / 51200) = -Real.log (51200 / 99383) := by
    rw [show ((99383 / 51200) : ℝ) = ((51200 / 99383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2831476569 / 1000000000) ≤ -Real.log (3017 / 51200) ∧
    -Real.log (3017 / 51200) ≤ (1415738287 / 500000000) := by
  have h := checkLog_sound (w := (183 / 6217)) (n := 12)
    (lo := (58887849 / 1000000000)) (hi := (1177757 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3017) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3017) = 1/(3017 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1415738287 / 500000000) (-2831476569 / 1000000000) (Real.log (3017 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (331525171 / 500000000) ≤ -Real.log (12800 / 24841) ∧
    -Real.log (12800 / 24841) ≤ (663050343 / 1000000000) := by
  have h := checkLog_sound (w := (12041 / 37641)) (n := 12)
    (lo := (331525171 / 500000000)) (hi := (663050343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24841 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24841 / 12800) = 1/(12800 / 24841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (331525171 / 500000000) (663050343 / 1000000000) (Real.log (24841 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24841 / 12800) = -Real.log (12800 / 24841) := by
    rw [show ((24841 / 12800) : ℝ) = ((12800 / 24841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (282519867 / 100000000) ≤ -Real.log (759 / 12800) ∧
    -Real.log (759 / 12800) ≤ (113007947 / 40000000) := by
  have h := checkLog_sound (w := (41 / 1559)) (n := 12)
    (lo := (1052199 / 20000000)) (hi := (52609951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 759) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 759) = 1/(759 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-113007947 / 40000000) (-282519867 / 100000000) (Real.log (759 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (680669659 / 1000000000) ≤ -Real.log (1250 / 2469) ∧
    -Real.log (1250 / 2469) ≤ (34033483 / 50000000) := by
  have h := checkLog_sound (w := (1219 / 3719)) (n := 12)
    (lo := (680669659 / 1000000000)) (hi := (34033483 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2469 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2469 / 1250) = 1/(1250 / 2469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (680669659 / 1000000000) (34033483 / 50000000) (Real.log (2469 / 1250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (2469 / 1250) = -Real.log (1250 / 2469) := by
    rw [show ((2469 / 1250) : ℝ) = ((1250 / 2469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3696911623 / 1000000000) ≤ -Real.log (31 / 1250) ∧
    -Real.log (31 / 1250) ≤ (3696911629 / 1000000000) := by
  have h := checkLog_sound (w := (129 / 1121)) (n := 12)
    (lo := (231175723 / 1000000000)) (hi := (57793931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 496) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(625 / 496) = 1/(31 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3696911629 / 1000000000) (-3696911623 / 1000000000) (Real.log (31 / 1250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (680745091 / 1000000000) ≤ -Real.log (1000000 / 1975349) ∧
    -Real.log (1000000 / 1975349) ≤ (170186273 / 250000000) := by
  have h := checkLog_sound (w := (975349 / 2975349)) (n := 12)
    (lo := (680745091 / 1000000000)) (hi := (170186273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975349 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975349 / 1000000) = 1/(1000000 / 1975349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (680745091 / 1000000000) (170186273 / 250000000) (Real.log (1975349 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1975349 / 1000000) = -Real.log (1000000 / 1975349) := by
    rw [show ((1975349 / 1000000) : ℝ) = ((1000000 / 1975349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (231433613 / 62500000) ≤ -Real.log (24651 / 1000000) ∧
    -Real.log (24651 / 1000000) ≤ (1851468907 / 500000000) := by
  have h := checkLog_sound (w := (6599 / 55901)) (n := 12)
    (lo := (59300477 / 250000000)) (hi := (237201909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24651) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24651) = 1/(24651 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1851468907 / 500000000) (-231433613 / 62500000) (Real.log (24651 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (680594727 / 1000000000) ≤ -Real.log (250000 / 493763) ∧
    -Real.log (250000 / 493763) ≤ (85074341 / 125000000) := by
  have h := checkLog_sound (w := (243763 / 743763)) (n := 12)
    (lo := (680594727 / 1000000000)) (hi := (85074341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493763 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493763 / 250000) = 1/(250000 / 493763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (680594727 / 1000000000) (85074341 / 125000000) (Real.log (493763 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (493763 / 250000) = -Real.log (250000 / 493763) := by
    rw [show ((493763 / 250000) : ℝ) = ((250000 / 493763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3690961617 / 1000000000) ≤ -Real.log (6237 / 250000) ∧
    -Real.log (6237 / 250000) ≤ (3690961623 / 1000000000) := by
  have h := checkLog_sound (w := (3151 / 28099)) (n := 12)
    (lo := (225225717 / 1000000000)) (hi := (112612859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12474) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12474) = 1/(6237 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3690961623 / 1000000000) (-3690961617 / 1000000000) (Real.log (6237 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680671177 / 1000000000) ≤ -Real.log (1000000 / 1975203) ∧
    -Real.log (1000000 / 1975203) ≤ (340335589 / 500000000) := by
  have h := checkLog_sound (w := (975203 / 2975203)) (n := 12)
    (lo := (680671177 / 1000000000)) (hi := (340335589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975203 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975203 / 1000000) = 1/(1000000 / 1975203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680671177 / 1000000000) (340335589 / 500000000) (Real.log (1975203 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1975203 / 1000000) = -Real.log (1000000 / 1975203) := by
    rw [show ((1975203 / 1000000) : ℝ) = ((1000000 / 1975203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1848516299 / 500000000) ≤ -Real.log (24797 / 1000000) ∧
    -Real.log (24797 / 1000000) ≤ (924258151 / 250000000) := by
  have h := checkLog_sound (w := (6453 / 56047)) (n := 12)
    (lo := (115648349 / 500000000)) (hi := (231296699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24797) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24797) = 1/(24797 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-924258151 / 250000000) (-1848516299 / 500000000) (Real.log (24797 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4377581281 / 1000000000) ≤ -Real.log (500000000000 / 39822580645161) ∧
    -Real.log (500000000000 / 39822580645161) ≤ (547197661 / 125000000) := by
  have h := checkLog_sound (w := (7822580645161 / 71822580645161)) (n := 12)
    (lo := (218698201 / 1000000000)) (hi := (109349101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39822580645161 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(39822580645161 / 32000000000000) = 1/(500000000000 / 39822580645161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4377581281 / 1000000000) (547197661 / 125000000) (Real.log (39822580645161 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (39822580645161 / 500000000000) = -Real.log (500000000000 / 39822580645161) := by
    rw [show ((39822580645161 / 500000000000) : ℝ) = ((500000000000 / 39822580645161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4383682899 / 1000000000) ≤ -Real.log (500000000000 / 40066305626547) ∧
    -Real.log (500000000000 / 40066305626547) ≤ (2191841453 / 500000000) := by
  have h := checkLog_sound (w := (8066305626547 / 72066305626547)) (n := 12)
    (lo := (224799819 / 1000000000)) (hi := (11239991 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40066305626547 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(40066305626547 / 32000000000000) = 1/(500000000000 / 40066305626547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4383682899 / 1000000000) (2191841453 / 500000000) (Real.log (40066305626547 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (40066305626547 / 500000000000) = -Real.log (500000000000 / 40066305626547) := by
    rw [show ((40066305626547 / 500000000000) : ℝ) = ((500000000000 / 40066305626547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (546444543 / 125000000) ≤ -Real.log (250000000000 / 19791686708353) ∧
    -Real.log (250000000000 / 19791686708353) ≤ (4371556351 / 1000000000) := by
  have h := checkLog_sound (w := (3791686708353 / 35791686708353)) (n := 12)
    (lo := (13292079 / 62500000)) (hi := (42534653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19791686708353 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(19791686708353 / 16000000000000) = 1/(250000000000 / 19791686708353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (546444543 / 125000000) (4371556351 / 1000000000) (Real.log (19791686708353 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (19791686708353 / 250000000000) = -Real.log (250000000000 / 19791686708353) := by
    rw [show ((19791686708353 / 250000000000) : ℝ) = ((250000000000 / 19791686708353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (175108151 / 40000000) ≤ -Real.log (500000000000 / 39827458966811) ∧
    -Real.log (500000000000 / 39827458966811) ≤ (2188851891 / 500000000) := by
  have h := checkLog_sound (w := (7827458966811 / 71827458966811)) (n := 12)
    (lo := (43764139 / 200000000)) (hi := (27352587 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39827458966811 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(39827458966811 / 32000000000000) = 1/(500000000000 / 39827458966811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (175108151 / 40000000) (2188851891 / 500000000) (Real.log (39827458966811 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (39827458966811 / 500000000000) = -Real.log (500000000000 / 39827458966811) := by
    rw [show ((39827458966811 / 500000000000) : ℝ) = ((500000000000 / 39827458966811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0058
