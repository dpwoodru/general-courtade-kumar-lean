import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0059
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

theorem reflection_log_1_neg : (42388249 / 62500000) ≤ -Real.log (25600 / 50441) ∧
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


theorem reflection_log_1 : Bounds (42388249 / 62500000) (135642397 / 200000000) (Real.log (50441 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50441 / 25600) = -Real.log (25600 / 50441) := by
    rw [show ((50441 / 25600) : ℝ) = ((25600 / 50441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (70366917 / 20000000) ≤ -Real.log (759 / 25600) ∧
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


theorem reflection_log_2 : Bounds (-27487077 / 7812500) (-70366917 / 20000000) (Real.log (759 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (678117811 / 1000000000) ≤ -Real.log (20480 / 40349) ∧
    -Real.log (20480 / 40349) ≤ (169529453 / 250000000) := by
  have h := checkLog_sound (w := (19869 / 60829)) (n := 12)
    (lo := (678117811 / 1000000000)) (hi := (169529453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40349 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40349 / 20480) = 1/(20480 / 40349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (678117811 / 1000000000) (169529453 / 250000000) (Real.log (40349 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (40349 / 20480) = -Real.log (20480 / 40349) := by
    rw [show ((40349 / 20480) : ℝ) = ((20480 / 40349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3512107117 / 1000000000) ≤ -Real.log (611 / 20480) ∧
    -Real.log (611 / 20480) ≤ (3512107123 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 1251)) (n := 12)
    (lo := (46371217 / 1000000000)) (hi := (23185609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 611) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 611) = 1/(611 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3512107123 / 1000000000) (-3512107117 / 1000000000) (Real.log (611 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (331525171 / 500000000) ≤ -Real.log (12800 / 24841) ∧
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


theorem reflection_log_5 : Bounds (331525171 / 500000000) (663050343 / 1000000000) (Real.log (24841 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24841 / 12800) = -Real.log (12800 / 24841) := by
    rw [show ((24841 / 12800) : ℝ) = ((12800 / 24841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (282519867 / 100000000) ≤ -Real.log (759 / 12800) ∧
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


theorem reflection_log_6 : Bounds (-113007947 / 40000000) (-282519867 / 100000000) (Real.log (759 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (165714777 / 250000000) ≤ -Real.log (10240 / 19869) ∧
    -Real.log (10240 / 19869) ≤ (662859109 / 1000000000) := by
  have h := checkLog_sound (w := (9629 / 30109)) (n := 12)
    (lo := (165714777 / 250000000)) (hi := (662859109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19869 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19869 / 10240) = 1/(10240 / 19869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (165714777 / 250000000) (662859109 / 1000000000) (Real.log (19869 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (19869 / 10240) = -Real.log (10240 / 19869) := by
    rw [show ((19869 / 10240) : ℝ) = ((10240 / 19869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2818959937 / 1000000000) ≤ -Real.log (611 / 10240) ∧
    -Real.log (611 / 10240) ≤ (1409479971 / 500000000) := by
  have h := checkLog_sound (w := (29 / 1251)) (n := 12)
    (lo := (46371217 / 1000000000)) (hi := (23185609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 611) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 611) = 1/(611 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1409479971 / 500000000) (-2818959937 / 1000000000) (Real.log (611 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (680594727 / 1000000000) ≤ -Real.log (250000 / 493763) ∧
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


theorem reflection_log_9 : Bounds (680594727 / 1000000000) (85074341 / 125000000) (Real.log (493763 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (493763 / 250000) = -Real.log (250000 / 493763) := by
    rw [show ((493763 / 250000) : ℝ) = ((250000 / 493763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3690961617 / 1000000000) ≤ -Real.log (6237 / 250000) ∧
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


theorem reflection_log_10 : Bounds (-3690961623 / 1000000000) (-3690961617 / 1000000000) (Real.log (6237 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136134033 / 200000000) ≤ -Real.log (1000000 / 1975201) ∧
    -Real.log (1000000 / 1975201) ≤ (340335083 / 500000000) := by
  have h := checkLog_sound (w := (975201 / 2975201)) (n := 12)
    (lo := (136134033 / 200000000)) (hi := (340335083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975201 / 1000000) = 1/(1000000 / 1975201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136134033 / 200000000) (340335083 / 500000000) (Real.log (1975201 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1975201 / 1000000) = -Real.log (1000000 / 1975201) := by
    rw [show ((1975201 / 1000000) : ℝ) = ((1000000 / 1975201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1848475973 / 500000000) ≤ -Real.log (24799 / 1000000) ∧
    -Real.log (24799 / 1000000) ≤ (231059497 / 62500000) := by
  have h := checkLog_sound (w := (6451 / 56049)) (n := 12)
    (lo := (115608023 / 500000000)) (hi := (231216047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24799) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24799) = 1/(24799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-231059497 / 62500000) (-1848475973 / 500000000) (Real.log (24799 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (85064847 / 125000000) ≤ -Real.log (500000 / 987451) ∧
    -Real.log (500000 / 987451) ≤ (680518777 / 1000000000) := by
  have h := checkLog_sound (w := (487451 / 1487451)) (n := 12)
    (lo := (85064847 / 125000000)) (hi := (680518777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987451 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987451 / 500000) = 1/(500000 / 987451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (85064847 / 125000000) (680518777 / 1000000000) (Real.log (987451 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (987451 / 500000) = -Real.log (500000 / 987451) := by
    rw [show ((987451 / 500000) : ℝ) = ((500000 / 987451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1842483557 / 500000000) ≤ -Real.log (12549 / 500000) ∧
    -Real.log (12549 / 500000) ≤ (46062089 / 12500000) := by
  have h := checkLog_sound (w := (1538 / 14087)) (n := 12)
    (lo := (109615607 / 500000000)) (hi := (43846243 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12549) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12549) = 1/(12549 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-46062089 / 12500000) (-1842483557 / 500000000) (Real.log (12549 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680595233 / 1000000000) ≤ -Real.log (1000000 / 1975053) ∧
    -Real.log (1000000 / 1975053) ≤ (340297617 / 500000000) := by
  have h := checkLog_sound (w := (975053 / 2975053)) (n := 12)
    (lo := (680595233 / 1000000000)) (hi := (340297617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975053 / 1000000) = 1/(1000000 / 1975053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680595233 / 1000000000) (340297617 / 500000000) (Real.log (1975053 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1975053 / 1000000) = -Real.log (1000000 / 1975053) := by
    rw [show ((1975053 / 1000000) : ℝ) = ((1000000 / 1975053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3691001701 / 1000000000) ≤ -Real.log (24947 / 1000000) ∧
    -Real.log (24947 / 1000000) ≤ (3691001707 / 1000000000) := by
  have h := checkLog_sound (w := (6303 / 56197)) (n := 12)
    (lo := (225265801 / 1000000000)) (hi := (112632901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24947) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24947) = 1/(24947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3691001707 / 1000000000) (-3691001701 / 1000000000) (Real.log (24947 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (546444543 / 125000000) ≤ -Real.log (250000000000 / 19791686708353) ∧
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


theorem reflection_log_17 : Bounds (546444543 / 125000000) (4371556351 / 1000000000) (Real.log (19791686708353 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (19791686708353 / 250000000000) = -Real.log (250000000000 / 19791686708353) := by
    rw [show ((19791686708353 / 250000000000) : ℝ) = ((250000000000 / 19791686708353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4377622111 / 1000000000) ≤ -Real.log (100000000000 / 7964841324247) ∧
    -Real.log (100000000000 / 7964841324247) ≤ (2188811059 / 500000000) := by
  have h := checkLog_sound (w := (1564841324247 / 14364841324247)) (n := 12)
    (lo := (218739031 / 1000000000)) (hi := (27342379 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7964841324247 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7964841324247 / 6400000000000) = 1/(100000000000 / 7964841324247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4377622111 / 1000000000) (2188811059 / 500000000) (Real.log (7964841324247 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7964841324247 / 100000000000) = -Real.log (100000000000 / 7964841324247) := by
    rw [show ((7964841324247 / 100000000000) : ℝ) = ((100000000000 / 7964841324247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (436548589 / 100000000) ≤ -Real.log (125000000000 / 9835953063989) ∧
    -Real.log (125000000000 / 9835953063989) ≤ (4365485897 / 1000000000) := by
  have h := checkLog_sound (w := (1835953063989 / 17835953063989)) (n := 12)
    (lo := (20660281 / 100000000)) (hi := (206602811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9835953063989 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9835953063989 / 8000000000000) = 1/(125000000000 / 9835953063989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (436548589 / 100000000) (4365485897 / 1000000000) (Real.log (9835953063989 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9835953063989 / 125000000000) = -Real.log (125000000000 / 9835953063989) := by
    rw [show ((9835953063989 / 125000000000) : ℝ) = ((125000000000 / 9835953063989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2185798467 / 500000000) ≤ -Real.log (100000000000 / 7916996031587) ∧
    -Real.log (100000000000 / 7916996031587) ≤ (4371596941 / 1000000000) := by
  have h := checkLog_sound (w := (1516996031587 / 14316996031587)) (n := 12)
    (lo := (106356927 / 500000000)) (hi := (42542771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7916996031587 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7916996031587 / 6400000000000) = 1/(100000000000 / 7916996031587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2185798467 / 500000000) (4371596941 / 1000000000) (Real.log (7916996031587 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7916996031587 / 100000000000) = -Real.log (100000000000 / 7916996031587) := by
    rw [show ((7916996031587 / 100000000000) : ℝ) = ((100000000000 / 7916996031587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0059
