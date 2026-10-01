import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0055
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

theorem reflection_log_1_neg : (678588591 / 1000000000) ≤ -Real.log (1280 / 2523) ∧
    -Real.log (1280 / 2523) ≤ (42411787 / 62500000) := by
  have h := checkLog_sound (w := (1243 / 3803)) (n := 12)
    (lo := (678588591 / 1000000000)) (hi := (42411787 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2523 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2523 / 1280) = 1/(1280 / 2523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (678588591 / 1000000000) (42411787 / 62500000) (Real.log (2523 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2523 / 1280) = -Real.log (1280 / 2523) := by
    rw [show ((2523 / 1280) : ℝ) = ((1280 / 2523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3543697441 / 1000000000) ≤ -Real.log (37 / 1280) ∧
    -Real.log (37 / 1280) ≤ (3543697447 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 37) = 1/(37 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3543697447 / 1000000000) (-3543697441 / 1000000000) (Real.log (37 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (678494453 / 1000000000) ≤ -Real.log (102400 / 201821) ∧
    -Real.log (102400 / 201821) ≤ (339247227 / 500000000) := by
  have h := checkLog_sound (w := (99421 / 304221)) (n := 12)
    (lo := (678494453 / 1000000000)) (hi := (339247227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201821 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201821 / 102400) = 1/(102400 / 201821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (678494453 / 1000000000) (339247227 / 500000000) (Real.log (201821 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201821 / 102400) = -Real.log (102400 / 201821) := by
    rw [show ((201821 / 102400) : ℝ) = ((102400 / 201821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (884324759 / 250000000) ≤ -Real.log (2979 / 102400) ∧
    -Real.log (2979 / 102400) ≤ (1768649521 / 500000000) := by
  have h := checkLog_sound (w := (221 / 6179)) (n := 12)
    (lo := (559087 / 7812500)) (hi := (71563137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2979) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2979) = 1/(2979 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1768649521 / 500000000) (-884324759 / 250000000) (Real.log (2979 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (132762983 / 200000000) ≤ -Real.log (640 / 1243) ∧
    -Real.log (640 / 1243) ≤ (165953729 / 250000000) := by
  have h := checkLog_sound (w := (603 / 1883)) (n := 12)
    (lo := (132762983 / 200000000)) (hi := (165953729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243 / 640) = 1/(640 / 1243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (132762983 / 200000000) (165953729 / 250000000) (Real.log (1243 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1243 / 640) = -Real.log (640 / 1243) := by
    rw [show ((1243 / 640) : ℝ) = ((640 / 1243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2850550261 / 1000000000) ≤ -Real.log (37 / 640) ∧
    -Real.log (37 / 640) ≤ (1425275133 / 500000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 37) = 1/(37 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1425275133 / 500000000) (-2850550261 / 1000000000) (Real.log (37 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (331811913 / 500000000) ≤ -Real.log (51200 / 99421) ∧
    -Real.log (51200 / 99421) ≤ (663623827 / 1000000000) := by
  have h := checkLog_sound (w := (48221 / 150621)) (n := 12)
    (lo := (331811913 / 500000000)) (hi := (663623827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99421 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99421 / 51200) = 1/(51200 / 99421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (331811913 / 500000000) (663623827 / 1000000000) (Real.log (99421 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99421 / 51200) = -Real.log (51200 / 99421) := by
    rw [show ((99421 / 51200) : ℝ) = ((51200 / 99421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (177759491 / 62500000) ≤ -Real.log (2979 / 51200) ∧
    -Real.log (2979 / 51200) ≤ (2844151861 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 6179)) (n := 12)
    (lo := (559087 / 7812500)) (hi := (71563137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2979) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2979) = 1/(2979 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2844151861 / 1000000000) (-177759491 / 62500000) (Real.log (2979 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (680894421 / 1000000000) ≤ -Real.log (250000 / 493911) ∧
    -Real.log (250000 / 493911) ≤ (340447211 / 500000000) := by
  have h := checkLog_sound (w := (243911 / 743911)) (n := 12)
    (lo := (680894421 / 1000000000)) (hi := (340447211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493911 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493911 / 250000) = 1/(250000 / 493911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (680894421 / 1000000000) (340447211 / 500000000) (Real.log (493911 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (493911 / 250000) = -Real.log (250000 / 493911) := by
    rw [show ((493911 / 250000) : ℝ) = ((250000 / 493911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (74299541 / 20000000) ≤ -Real.log (6089 / 250000) ∧
    -Real.log (6089 / 250000) ≤ (116093033 / 31250000) := by
  have h := checkLog_sound (w := (3447 / 27803)) (n := 12)
    (lo := (4984823 / 20000000)) (hi := (249241151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12178) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12178) = 1/(6089 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-116093033 / 31250000) (-74299541 / 20000000) (Real.log (6089 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170242459 / 250000000) ≤ -Real.log (1000000 / 1975793) ∧
    -Real.log (1000000 / 1975793) ≤ (680969837 / 1000000000) := by
  have h := checkLog_sound (w := (975793 / 2975793)) (n := 12)
    (lo := (170242459 / 250000000)) (hi := (680969837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975793 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975793 / 1000000) = 1/(1000000 / 1975793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170242459 / 250000000) (680969837 / 1000000000) (Real.log (1975793 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1975793 / 1000000) = -Real.log (1000000 / 1975793) := by
    rw [show ((1975793 / 1000000) : ℝ) = ((1000000 / 1975793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (930278357 / 250000000) ≤ -Real.log (24207 / 1000000) ∧
    -Real.log (24207 / 1000000) ≤ (1860556717 / 500000000) := by
  have h := checkLog_sound (w := (7043 / 55457)) (n := 12)
    (lo := (31922191 / 125000000)) (hi := (255377529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24207) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24207) = 1/(24207 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1860556717 / 500000000) (-930278357 / 250000000) (Real.log (24207 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (680822543 / 1000000000) ≤ -Real.log (500000 / 987751) ∧
    -Real.log (500000 / 987751) ≤ (42551409 / 62500000) := by
  have h := checkLog_sound (w := (487751 / 1487751)) (n := 12)
    (lo := (680822543 / 1000000000)) (hi := (42551409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987751 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987751 / 500000) = 1/(500000 / 987751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (680822543 / 1000000000) (42551409 / 62500000) (Real.log (987751 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (987751 / 500000) = -Real.log (500000 / 987751) := by
    rw [show ((987751 / 500000) : ℝ) = ((500000 / 987751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1854581897 / 500000000) ≤ -Real.log (12249 / 500000) ∧
    -Real.log (12249 / 500000) ≤ (18545819 / 5000000) := by
  have h := checkLog_sound (w := (1688 / 13937)) (n := 12)
    (lo := (121713947 / 500000000)) (hi := (48685579 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12249) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12249) = 1/(12249 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-18545819 / 5000000) (-1854581897 / 500000000) (Real.log (12249 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (21278093 / 31250000) ≤ -Real.log (1000000 / 1975653) ∧
    -Real.log (1000000 / 1975653) ≤ (680898977 / 1000000000) := by
  have h := checkLog_sound (w := (975653 / 2975653)) (n := 12)
    (lo := (21278093 / 31250000)) (hi := (680898977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975653 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975653 / 1000000) = 1/(1000000 / 1975653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21278093 / 31250000) (680898977 / 1000000000) (Real.log (1975653 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1975653 / 1000000) = -Real.log (1000000 / 1975653) := by
    rw [show ((1975653 / 1000000) : ℝ) = ((1000000 / 1975653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3715346637 / 1000000000) ≤ -Real.log (24347 / 1000000) ∧
    -Real.log (24347 / 1000000) ≤ (3715346643 / 1000000000) := by
  have h := checkLog_sound (w := (6903 / 55597)) (n := 12)
    (lo := (249610737 / 1000000000)) (hi := (124805369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24347) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24347) = 1/(24347 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3715346643 / 1000000000) (-3715346637 / 1000000000) (Real.log (24347 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4395871471 / 1000000000) ≤ -Real.log (250000000000 / 20278822466743) ∧
    -Real.log (250000000000 / 20278822466743) ≤ (2197935739 / 500000000) := by
  have h := checkLog_sound (w := (4278822466743 / 36278822466743)) (n := 12)
    (lo := (236988391 / 1000000000)) (hi := (29623549 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20278822466743 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20278822466743 / 16000000000000) = 1/(250000000000 / 20278822466743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4395871471 / 1000000000) (2197935739 / 500000000) (Real.log (20278822466743 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (20278822466743 / 250000000000) = -Real.log (250000000000 / 20278822466743) := by
    rw [show ((20278822466743 / 250000000000) : ℝ) = ((250000000000 / 20278822466743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (68782551 / 15625000) ≤ -Real.log (500000000000 / 40810364770521) ∧
    -Real.log (500000000000 / 40810364770521) ≤ (4402083271 / 1000000000) := by
  have h := checkLog_sound (w := (8810364770521 / 72810364770521)) (n := 12)
    (lo := (30400023 / 125000000)) (hi := (48640037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40810364770521 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(40810364770521 / 32000000000000) = 1/(500000000000 / 40810364770521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (68782551 / 15625000) (4402083271 / 1000000000) (Real.log (40810364770521 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (40810364770521 / 500000000000) = -Real.log (500000000000 / 40810364770521) := by
    rw [show ((40810364770521 / 500000000000) : ℝ) = ((500000000000 / 40810364770521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4389986337 / 1000000000) ≤ -Real.log (125000000000 / 10079914686913) ∧
    -Real.log (125000000000 / 10079914686913) ≤ (548748293 / 125000000) := by
  have h := checkLog_sound (w := (2079914686913 / 18079914686913)) (n := 12)
    (lo := (231103257 / 1000000000)) (hi := (115551629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10079914686913 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10079914686913 / 8000000000000) = 1/(125000000000 / 10079914686913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4389986337 / 1000000000) (548748293 / 125000000) (Real.log (10079914686913 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (10079914686913 / 125000000000) = -Real.log (125000000000 / 10079914686913) := by
    rw [show ((10079914686913 / 125000000000) : ℝ) = ((125000000000 / 10079914686913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4396245613 / 1000000000) ≤ -Real.log (62500000000 / 5071602764201) ∧
    -Real.log (62500000000 / 5071602764201) ≤ (219812281 / 50000000) := by
  have h := checkLog_sound (w := (1071602764201 / 9071602764201)) (n := 12)
    (lo := (237362533 / 1000000000)) (hi := (118681267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5071602764201 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5071602764201 / 4000000000000) = 1/(62500000000 / 5071602764201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4396245613 / 1000000000) (219812281 / 50000000) (Real.log (5071602764201 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5071602764201 / 62500000000) = -Real.log (62500000000 / 5071602764201) := by
    rw [show ((5071602764201 / 62500000000) : ℝ) = ((62500000000 / 5071602764201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0055
