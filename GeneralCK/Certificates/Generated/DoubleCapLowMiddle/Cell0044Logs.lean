import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0044
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

theorem reflection_log_1_neg : (679623529 / 1000000000) ≤ -Real.log (102400 / 202049) ∧
    -Real.log (102400 / 202049) ≤ (67962353 / 100000000) := by
  have h := checkLog_sound (w := (99649 / 304449)) (n := 12)
    (lo := (679623529 / 1000000000)) (hi := (67962353 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202049 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202049 / 102400) = 1/(102400 / 202049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (679623529 / 1000000000) (67962353 / 100000000) (Real.log (202049 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202049 / 102400) = -Real.log (102400 / 202049) := by
    rw [show ((202049 / 102400) : ℝ) = ((102400 / 202049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3616922227 / 1000000000) ≤ -Real.log (2751 / 102400) ∧
    -Real.log (2751 / 102400) ≤ (3616922233 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 5951)) (n := 12)
    (lo := (151186327 / 1000000000)) (hi := (18898291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2751) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2751) = 1/(2751 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3616922233 / 1000000000) (-3616922227 / 1000000000) (Real.log (2751 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (42470593 / 62500000) ≤ -Real.log (10240 / 20203) ∧
    -Real.log (10240 / 20203) ≤ (679529489 / 1000000000) := by
  have h := checkLog_sound (w := (9963 / 30443)) (n := 12)
    (lo := (42470593 / 62500000)) (hi := (679529489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20203 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20203 / 10240) = 1/(10240 / 20203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (42470593 / 62500000) (679529489 / 1000000000) (Real.log (20203 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (20203 / 10240) = -Real.log (10240 / 20203) := by
    rw [show ((20203 / 10240) : ℝ) = ((10240 / 20203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3610039389 / 1000000000) ≤ -Real.log (277 / 10240) ∧
    -Real.log (277 / 10240) ≤ (722007879 / 200000000) := by
  have h := checkLog_sound (w := (43 / 597)) (n := 12)
    (lo := (144303489 / 1000000000)) (hi := (14430349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 277) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(320 / 277) = 1/(277 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-722007879 / 200000000) (-3610039389 / 1000000000) (Real.log (277 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (665914479 / 1000000000) ≤ -Real.log (51200 / 99649) ∧
    -Real.log (51200 / 99649) ≤ (8323931 / 12500000) := by
  have h := checkLog_sound (w := (48449 / 150849)) (n := 12)
    (lo := (665914479 / 1000000000)) (hi := (8323931 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99649 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99649 / 51200) = 1/(51200 / 99649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (665914479 / 1000000000) (8323931 / 12500000) (Real.log (99649 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99649 / 51200) = -Real.log (51200 / 99649) := by
    rw [show ((99649 / 51200) : ℝ) = ((51200 / 99649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2923775047 / 1000000000) ≤ -Real.log (2751 / 51200) ∧
    -Real.log (2751 / 51200) ≤ (730943763 / 250000000) := by
  have h := checkLog_sound (w := (449 / 5951)) (n := 12)
    (lo := (151186327 / 1000000000)) (hi := (18898291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2751) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2751) = 1/(2751 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-730943763 / 250000000) (-2923775047 / 1000000000) (Real.log (2751 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41607737 / 62500000) ≤ -Real.log (5120 / 9963) ∧
    -Real.log (5120 / 9963) ≤ (665723793 / 1000000000) := by
  have h := checkLog_sound (w := (4843 / 15083)) (n := 12)
    (lo := (41607737 / 62500000)) (hi := (665723793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9963 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9963 / 5120) = 1/(5120 / 9963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41607737 / 62500000) (665723793 / 1000000000) (Real.log (9963 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (9963 / 5120) = -Real.log (5120 / 9963) := by
    rw [show ((9963 / 5120) : ℝ) = ((5120 / 9963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2916892209 / 1000000000) ≤ -Real.log (277 / 5120) ∧
    -Real.log (277 / 5120) ≤ (1458446107 / 500000000) := by
  have h := checkLog_sound (w := (43 / 597)) (n := 12)
    (lo := (144303489 / 1000000000)) (hi := (14430349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 277) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 277) = 1/(277 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1458446107 / 500000000) (-2916892209 / 1000000000) (Real.log (277 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (136344129 / 200000000) ≤ -Real.log (1000000 / 1977277) ∧
    -Real.log (1000000 / 1977277) ≤ (340860323 / 500000000) := by
  have h := checkLog_sound (w := (977277 / 2977277)) (n := 12)
    (lo := (136344129 / 200000000)) (hi := (340860323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977277 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977277 / 1000000) = 1/(1000000 / 1977277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (136344129 / 200000000) (340860323 / 500000000) (Real.log (1977277 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1977277 / 1000000) = -Real.log (1000000 / 1977277) := by
    rw [show ((1977277 / 1000000) : ℝ) = ((1000000 / 1977277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (236523603 / 62500000) ≤ -Real.log (22723 / 1000000) ∧
    -Real.log (22723 / 1000000) ≤ (1892188827 / 500000000) := by
  have h := checkLog_sound (w := (8527 / 53973)) (n := 12)
    (lo := (79660437 / 250000000)) (hi := (318641749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22723) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22723) = 1/(22723 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1892188827 / 500000000) (-236523603 / 62500000) (Real.log (22723 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (340897999 / 500000000) ≤ -Real.log (500000 / 988713) ∧
    -Real.log (500000 / 988713) ≤ (681795999 / 1000000000) := by
  have h := checkLog_sound (w := (488713 / 1488713)) (n := 12)
    (lo := (340897999 / 500000000)) (hi := (681795999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988713 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988713 / 500000) = 1/(500000 / 988713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (340897999 / 500000000) (681795999 / 1000000000) (Real.log (988713 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (988713 / 500000) = -Real.log (500000 / 988713) := by
    rw [show ((988713 / 500000) : ℝ) = ((500000 / 988713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1895478237 / 500000000) ≤ -Real.log (11287 / 500000) ∧
    -Real.log (11287 / 500000) ≤ (11846739 / 3125000) := by
  have h := checkLog_sound (w := (2169 / 13456)) (n := 12)
    (lo := (162610287 / 500000000)) (hi := (13008823 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11287) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11287) = 1/(11287 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-11846739 / 3125000) (-1895478237 / 500000000) (Real.log (11287 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (85207431 / 125000000) ≤ -Real.log (250000 / 494289) ∧
    -Real.log (250000 / 494289) ≤ (681659449 / 1000000000) := by
  have h := checkLog_sound (w := (244289 / 744289)) (n := 12)
    (lo := (85207431 / 125000000)) (hi := (681659449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494289 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494289 / 250000) = 1/(250000 / 494289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (85207431 / 125000000) (681659449 / 1000000000) (Real.log (494289 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (494289 / 250000) = -Real.log (250000 / 494289) := by
    rw [show ((494289 / 250000) : ℝ) = ((250000 / 494289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (151162671 / 40000000) ≤ -Real.log (5711 / 250000) ∧
    -Real.log (5711 / 250000) ≤ (3779066781 / 1000000000) := by
  have h := checkLog_sound (w := (4203 / 27047)) (n := 12)
    (lo := (2506647 / 8000000)) (hi := (78332719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11422) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11422) = 1/(5711 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3779066781 / 1000000000) (-151162671 / 40000000) (Real.log (5711 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681736323 / 1000000000) ≤ -Real.log (250000 / 494327) ∧
    -Real.log (250000 / 494327) ≤ (170434081 / 250000000) := by
  have h := checkLog_sound (w := (244327 / 744327)) (n := 12)
    (lo := (681736323 / 1000000000)) (hi := (170434081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494327 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494327 / 250000) = 1/(250000 / 494327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681736323 / 1000000000) (170434081 / 250000000) (Real.log (494327 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (494327 / 250000) = -Real.log (250000 / 494327) := by
    rw [show ((494327 / 250000) : ℝ) = ((250000 / 494327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (946435709 / 250000000) ≤ -Real.log (5673 / 250000) ∧
    -Real.log (5673 / 250000) ≤ (1892871421 / 500000000) := by
  have h := checkLog_sound (w := (4279 / 26971)) (n := 12)
    (lo := (40000867 / 125000000)) (hi := (320006937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11346) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11346) = 1/(5673 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1892871421 / 500000000) (-946435709 / 250000000) (Real.log (5673 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4466098293 / 1000000000) ≤ -Real.log (125000000000 / 10877068388857) ∧
    -Real.log (125000000000 / 10877068388857) ≤ (44660983 / 10000000) := by
  have h := checkLog_sound (w := (2877068388857 / 18877068388857)) (n := 12)
    (lo := (307215213 / 1000000000)) (hi := (153607607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10877068388857 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10877068388857 / 8000000000000) = 1/(125000000000 / 10877068388857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4466098293 / 1000000000) (44660983 / 10000000) (Real.log (10877068388857 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10877068388857 / 125000000000) = -Real.log (125000000000 / 10877068388857) := by
    rw [show ((10877068388857 / 125000000000) : ℝ) = ((125000000000 / 10877068388857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4472752473 / 1000000000) ≤ -Real.log (500000000000 / 43798750775229) ∧
    -Real.log (500000000000 / 43798750775229) ≤ (27954703 / 6250000) := by
  have h := checkLog_sound (w := (11798750775229 / 75798750775229)) (n := 12)
    (lo := (313869393 / 1000000000)) (hi := (156934697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43798750775229 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(43798750775229 / 32000000000000) = 1/(500000000000 / 43798750775229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4472752473 / 1000000000) (27954703 / 6250000) (Real.log (43798750775229 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (43798750775229 / 500000000000) = -Real.log (500000000000 / 43798750775229) := by
    rw [show ((43798750775229 / 500000000000) : ℝ) = ((500000000000 / 43798750775229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4460726223 / 1000000000) ≤ -Real.log (100000000000 / 8655034144633) ∧
    -Real.log (100000000000 / 8655034144633) ≤ (446072623 / 100000000) := by
  have h := checkLog_sound (w := (2255034144633 / 15055034144633)) (n := 12)
    (lo := (301843143 / 1000000000)) (hi := (37730393 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8655034144633 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8655034144633 / 6400000000000) = 1/(100000000000 / 8655034144633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4460726223 / 1000000000) (446072623 / 100000000) (Real.log (8655034144633 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8655034144633 / 100000000000) = -Real.log (100000000000 / 8655034144633) := by
    rw [show ((8655034144633 / 100000000000) : ℝ) = ((100000000000 / 8655034144633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4467479159 / 1000000000) ≤ -Real.log (250000000000 / 21784197073859) ∧
    -Real.log (250000000000 / 21784197073859) ≤ (2233739583 / 500000000) := by
  have h := checkLog_sound (w := (5784197073859 / 37784197073859)) (n := 12)
    (lo := (308596079 / 1000000000)) (hi := (3857451 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21784197073859 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(21784197073859 / 16000000000000) = 1/(250000000000 / 21784197073859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4467479159 / 1000000000) (2233739583 / 500000000) (Real.log (21784197073859 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (21784197073859 / 250000000000) = -Real.log (250000000000 / 21784197073859) := by
    rw [show ((21784197073859 / 250000000000) : ℝ) = ((250000000000 / 21784197073859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0044
