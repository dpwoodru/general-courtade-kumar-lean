import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2368_neg : (167213 / 1000000000) ≤ -Real.log (1249791 / 1250000) ∧
    -Real.log (1249791 / 1250000) ≤ (83607 / 500000000) := by
  have h := checkLog_sound (w := (209 / 2499791)) (n := 12)
    (lo := (167213 / 1000000000)) (hi := (83607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249791) = 1/(1249791 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2368 : Bounds (-83607 / 500000000) (-167213 / 1000000000) (Real.log (1249791 / 1250000)) := by
  have h := reflection_log_2368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2369_neg : (2517417 / 31250000) ≤ -Real.log (1000000 / 1083891) ∧
    -Real.log (1000000 / 1083891) ≤ (16111469 / 200000000) := by
  have h := checkLog_sound (w := (83891 / 2083891)) (n := 12)
    (lo := (2517417 / 31250000)) (hi := (16111469 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083891 / 1000000) = 1/(1000000 / 1083891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2369 : Bounds (2517417 / 31250000) (16111469 / 200000000) (Real.log (1083891 / 1000000)) := by
  have h := reflection_log_2369_neg
  have he : Real.log (1083891 / 1000000) = -Real.log (1000000 / 1083891) := by
    rw [show ((1083891 / 1000000) : ℝ) = ((1000000 / 1083891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2370_neg : (3504797 / 40000000) ≤ -Real.log (916109 / 1000000) ∧
    -Real.log (916109 / 1000000) ≤ (43809963 / 500000000) := by
  have h := checkLog_sound (w := (83891 / 1916109)) (n := 12)
    (lo := (3504797 / 40000000)) (hi := (43809963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916109) = 1/(916109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2370 : Bounds (-43809963 / 500000000) (-3504797 / 40000000) (Real.log (916109 / 1000000)) := by
  have h := reflection_log_2370_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2371_neg : (80758451 / 1000000000) ≤ -Real.log (1000000 / 1084109) ∧
    -Real.log (1000000 / 1084109) ≤ (20189613 / 250000000) := by
  have h := checkLog_sound (w := (84109 / 2084109)) (n := 12)
    (lo := (80758451 / 1000000000)) (hi := (20189613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084109 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084109 / 1000000) = 1/(1000000 / 1084109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2371 : Bounds (80758451 / 1000000000) (20189613 / 250000000) (Real.log (1084109 / 1000000)) := by
  have h := reflection_log_2371_neg
  have he : Real.log (1084109 / 1000000) = -Real.log (1000000 / 1084109) := by
    rw [show ((1084109 / 1000000) : ℝ) = ((1000000 / 1084109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2372_neg : (87857917 / 1000000000) ≤ -Real.log (915891 / 1000000) ∧
    -Real.log (915891 / 1000000) ≤ (43928959 / 500000000) := by
  have h := checkLog_sound (w := (84109 / 1915891)) (n := 12)
    (lo := (87857917 / 1000000000)) (hi := (43928959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915891) = 1/(915891 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2372 : Bounds (-43928959 / 500000000) (-87857917 / 1000000000) (Real.log (915891 / 1000000)) := by
  have h := reflection_log_2372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2373_neg : (1419893 / 200000000) ≤ -Real.log (992925676119 / 1000000000000) ∧
    -Real.log (992925676119 / 1000000000000) ≤ (3549733 / 500000000) := by
  have h := checkLog_sound (w := (7074323881 / 1992925676119)) (n := 12)
    (lo := (1419893 / 200000000)) (hi := (3549733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992925676119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992925676119) = 1/(992925676119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2373 : Bounds (-3549733 / 500000000) (-1419893 / 200000000) (Real.log (992925676119 / 1000000000000)) := by
  have h := reflection_log_2373_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2374_neg : (7062581 / 1000000000) ≤ -Real.log (992962300119 / 1000000000000) ∧
    -Real.log (992962300119 / 1000000000000) ≤ (3531291 / 500000000) := by
  have h := checkLog_sound (w := (7037699881 / 1992962300119)) (n := 12)
    (lo := (7062581 / 1000000000)) (hi := (3531291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992962300119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992962300119) = 1/(992962300119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2374 : Bounds (-3531291 / 500000000) (-7062581 / 1000000000) (Real.log (992962300119 / 1000000000000)) := by
  have h := reflection_log_2374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2375_neg : (16817727 / 100000000) ≤ -Real.log (62500000000 / 73946645541) ∧
    -Real.log (62500000000 / 73946645541) ≤ (168177271 / 1000000000) := by
  have h := checkLog_sound (w := (11446645541 / 136446645541)) (n := 12)
    (lo := (16817727 / 100000000)) (hi := (168177271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73946645541 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73946645541 / 62500000000) = 1/(62500000000 / 73946645541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2375 : Bounds (16817727 / 100000000) (168177271 / 1000000000) (Real.log (73946645541 / 62500000000)) := by
  have h := reflection_log_2375_neg
  have he : Real.log (73946645541 / 62500000000) = -Real.log (62500000000 / 73946645541) := by
    rw [show ((73946645541 / 62500000000) : ℝ) = ((62500000000 / 73946645541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2376_neg : (10538523 / 62500000) ≤ -Real.log (250000000000 / 295916490063) ∧
    -Real.log (250000000000 / 295916490063) ≤ (168616369 / 1000000000) := by
  have h := checkLog_sound (w := (45916490063 / 545916490063)) (n := 12)
    (lo := (10538523 / 62500000)) (hi := (168616369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295916490063 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295916490063 / 250000000000) = 1/(250000000000 / 295916490063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2376 : Bounds (10538523 / 62500000) (168616369 / 1000000000) (Real.log (295916490063 / 250000000000)) := by
  have h := reflection_log_2376_neg
  have he : Real.log (295916490063 / 250000000000) = -Real.log (250000000000 / 295916490063) := by
    rw [show ((295916490063 / 250000000000) : ℝ) = ((250000000000 / 295916490063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2377_neg : (337363731 / 1000000000) ≤ -Real.log (62500000000 / 87578040581) ∧
    -Real.log (62500000000 / 87578040581) ≤ (84340933 / 250000000) := by
  have h := checkLog_sound (w := (25078040581 / 150078040581)) (n := 12)
    (lo := (337363731 / 1000000000)) (hi := (84340933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87578040581 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87578040581 / 62500000000) = 1/(62500000000 / 87578040581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2377 : Bounds (337363731 / 1000000000) (84340933 / 250000000) (Real.log (87578040581 / 62500000000)) := by
  have h := reflection_log_2377_neg
  have he : Real.log (87578040581 / 62500000000) = -Real.log (62500000000 / 87578040581) := by
    rw [show ((87578040581 / 62500000000) : ℝ) = ((62500000000 / 87578040581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2378_neg : (337569479 / 1000000000) ≤ -Real.log (100000000000 / 140153698367) ∧
    -Real.log (100000000000 / 140153698367) ≤ (8439237 / 25000000) := by
  have h := checkLog_sound (w := (40153698367 / 240153698367)) (n := 12)
    (lo := (337569479 / 1000000000)) (hi := (8439237 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140153698367 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140153698367 / 100000000000) = 1/(100000000000 / 140153698367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2378 : Bounds (337569479 / 1000000000) (8439237 / 25000000) (Real.log (140153698367 / 100000000000)) := by
  have h := reflection_log_2378_neg
  have he : Real.log (140153698367 / 100000000000) = -Real.log (100000000000 / 140153698367) := by
    rw [show ((140153698367 / 100000000000) : ℝ) = ((100000000000 / 140153698367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2379_neg : (154693389 / 1000000000) ≤ -Real.log (10000 / 11673) ∧
    -Real.log (10000 / 11673) ≤ (15469339 / 100000000) := by
  have h := checkLog_sound (w := (1673 / 21673)) (n := 12)
    (lo := (154693389 / 1000000000)) (hi := (15469339 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11673 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11673 / 10000) = 1/(10000 / 11673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2379 : Bounds (154693389 / 1000000000) (15469339 / 100000000) (Real.log (11673 / 10000)) := by
  have h := reflection_log_2379_neg
  have he : Real.log (11673 / 10000) = -Real.log (10000 / 11673) := by
    rw [show ((11673 / 10000) : ℝ) = ((10000 / 11673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2380_neg : (36616369 / 200000000) ≤ -Real.log (8327 / 10000) ∧
    -Real.log (8327 / 10000) ≤ (91540923 / 500000000) := by
  have h := checkLog_sound (w := (1673 / 18327)) (n := 12)
    (lo := (36616369 / 200000000)) (hi := (91540923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8327) = 1/(8327 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2380 : Bounds (-91540923 / 500000000) (-36616369 / 200000000) (Real.log (8327 / 10000)) := by
  have h := reflection_log_2380_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2381_neg : (83643 / 500000000) ≤ -Real.log (10000000 / 10001673) ∧
    -Real.log (10000000 / 10001673) ≤ (167287 / 1000000000) := by
  have h := checkLog_sound (w := (1673 / 20001673)) (n := 12)
    (lo := (83643 / 500000000)) (hi := (167287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001673 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001673 / 10000000) = 1/(10000000 / 10001673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2381 : Bounds (83643 / 500000000) (167287 / 1000000000) (Real.log (10001673 / 10000000)) := by
  have h := reflection_log_2381_neg
  have he : Real.log (10001673 / 10000000) = -Real.log (10000000 / 10001673) := by
    rw [show ((10001673 / 10000000) : ℝ) = ((10000000 / 10001673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2382_neg : (167313 / 1000000000) ≤ -Real.log (9998327 / 10000000) ∧
    -Real.log (9998327 / 10000000) ≤ (83657 / 500000000) := by
  have h := checkLog_sound (w := (1673 / 19998327)) (n := 12)
    (lo := (167313 / 1000000000)) (hi := (83657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998327) = 1/(9998327 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2382 : Bounds (-83657 / 500000000) (-167313 / 1000000000) (Real.log (9998327 / 10000000)) := by
  have h := reflection_log_2382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2383_neg : (80603473 / 1000000000) ≤ -Real.log (1000000 / 1083941) ∧
    -Real.log (1000000 / 1083941) ≤ (40301737 / 500000000) := by
  have h := checkLog_sound (w := (83941 / 2083941)) (n := 12)
    (lo := (80603473 / 1000000000)) (hi := (40301737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083941 / 1000000) = 1/(1000000 / 1083941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2383 : Bounds (80603473 / 1000000000) (40301737 / 500000000) (Real.log (1083941 / 1000000)) := by
  have h := reflection_log_2383_neg
  have he : Real.log (1083941 / 1000000) = -Real.log (1000000 / 1083941) := by
    rw [show ((1083941 / 1000000) : ℝ) = ((1000000 / 1083941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2384_neg : (17534901 / 200000000) ≤ -Real.log (916059 / 1000000) ∧
    -Real.log (916059 / 1000000) ≤ (43837253 / 500000000) := by
  have h := checkLog_sound (w := (83941 / 1916059)) (n := 12)
    (lo := (17534901 / 200000000)) (hi := (43837253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916059) = 1/(916059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2384 : Bounds (-43837253 / 500000000) (-17534901 / 200000000) (Real.log (916059 / 1000000)) := by
  have h := reflection_log_2384_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2385_neg : (80804571 / 1000000000) ≤ -Real.log (1000000 / 1084159) ∧
    -Real.log (1000000 / 1084159) ≤ (20201143 / 250000000) := by
  have h := checkLog_sound (w := (84159 / 2084159)) (n := 12)
    (lo := (80804571 / 1000000000)) (hi := (20201143 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084159 / 1000000) = 1/(1000000 / 1084159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2385 : Bounds (80804571 / 1000000000) (20201143 / 250000000) (Real.log (1084159 / 1000000)) := by
  have h := reflection_log_2385_neg
  have he : Real.log (1084159 / 1000000) = -Real.log (1000000 / 1084159) := by
    rw [show ((1084159 / 1000000) : ℝ) = ((1000000 / 1084159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2386_neg : (8791251 / 100000000) ≤ -Real.log (915841 / 1000000) ∧
    -Real.log (915841 / 1000000) ≤ (87912511 / 1000000000) := by
  have h := checkLog_sound (w := (84159 / 1915841)) (n := 12)
    (lo := (8791251 / 100000000)) (hi := (87912511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915841) = 1/(915841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2386 : Bounds (-87912511 / 1000000000) (-8791251 / 100000000) (Real.log (915841 / 1000000)) := by
  have h := reflection_log_2386_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2387_neg : (3553969 / 500000000) ≤ -Real.log (992917262719 / 1000000000000) ∧
    -Real.log (992917262719 / 1000000000000) ≤ (7107939 / 1000000000) := by
  have h := checkLog_sound (w := (7082737281 / 1992917262719)) (n := 12)
    (lo := (3553969 / 500000000)) (hi := (7107939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992917262719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992917262719) = 1/(992917262719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2387 : Bounds (-7107939 / 1000000000) (-3553969 / 500000000) (Real.log (992917262719 / 1000000000000)) := by
  have h := reflection_log_2387_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2388_neg : (883879 / 125000000) ≤ -Real.log (992953908519 / 1000000000000) ∧
    -Real.log (992953908519 / 1000000000000) ≤ (7071033 / 1000000000) := by
  have h := checkLog_sound (w := (7046091481 / 1992953908519)) (n := 12)
    (lo := (883879 / 125000000)) (hi := (7071033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992953908519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992953908519) = 1/(992953908519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2388 : Bounds (-7071033 / 1000000000) (-883879 / 125000000) (Real.log (992953908519 / 1000000000000)) := by
  have h := reflection_log_2388_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2389_neg : (168277979 / 1000000000) ≤ -Real.log (500000000000 / 591632744179) ∧
    -Real.log (500000000000 / 591632744179) ≤ (8413899 / 50000000) := by
  have h := checkLog_sound (w := (91632744179 / 1091632744179)) (n := 12)
    (lo := (168277979 / 1000000000)) (hi := (8413899 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591632744179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591632744179 / 500000000000) = 1/(500000000000 / 591632744179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2389 : Bounds (168277979 / 1000000000) (8413899 / 50000000) (Real.log (591632744179 / 500000000000)) := by
  have h := reflection_log_2389_neg
  have he : Real.log (591632744179 / 500000000000) = -Real.log (500000000000 / 591632744179) := by
    rw [show ((591632744179 / 500000000000) : ℝ) = ((500000000000 / 591632744179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2390_neg : (168717081 / 1000000000) ≤ -Real.log (500000000000 / 591892588343) ∧
    -Real.log (500000000000 / 591892588343) ≤ (84358541 / 500000000) := by
  have h := checkLog_sound (w := (91892588343 / 1091892588343)) (n := 12)
    (lo := (168717081 / 1000000000)) (hi := (84358541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591892588343 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591892588343 / 500000000000) = 1/(500000000000 / 591892588343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2390 : Bounds (168717081 / 1000000000) (84358541 / 500000000) (Real.log (591892588343 / 500000000000)) := by
  have h := reflection_log_2390_neg
  have he : Real.log (591892588343 / 500000000000) = -Real.log (500000000000 / 591892588343) := by
    rw [show ((591892588343 / 500000000000) : ℝ) = ((500000000000 / 591892588343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2391_neg : (337569479 / 1000000000) ≤ -Real.log (250000000000 / 350384245917) ∧
    -Real.log (250000000000 / 350384245917) ≤ (8439237 / 25000000) := by
  have h := checkLog_sound (w := (100384245917 / 600384245917)) (n := 12)
    (lo := (337569479 / 1000000000)) (hi := (8439237 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350384245917 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350384245917 / 250000000000) = 1/(250000000000 / 350384245917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2391 : Bounds (337569479 / 1000000000) (8439237 / 25000000) (Real.log (350384245917 / 250000000000)) := by
  have h := reflection_log_2391_neg
  have he : Real.log (350384245917 / 250000000000) = -Real.log (250000000000 / 350384245917) := by
    rw [show ((350384245917 / 250000000000) : ℝ) = ((250000000000 / 350384245917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2392_neg : (67555047 / 200000000) ≤ -Real.log (31250000000 / 43807043353) ∧
    -Real.log (31250000000 / 43807043353) ≤ (84443809 / 250000000) := by
  have h := checkLog_sound (w := (12557043353 / 75057043353)) (n := 12)
    (lo := (67555047 / 200000000)) (hi := (84443809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43807043353 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43807043353 / 31250000000) = 1/(31250000000 / 43807043353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2392 : Bounds (67555047 / 200000000) (84443809 / 250000000) (Real.log (43807043353 / 31250000000)) := by
  have h := reflection_log_2392_neg
  have he : Real.log (43807043353 / 31250000000) = -Real.log (31250000000 / 43807043353) := by
    rw [show ((43807043353 / 31250000000) : ℝ) = ((31250000000 / 43807043353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2393_neg : (154779053 / 1000000000) ≤ -Real.log (5000 / 5837) ∧
    -Real.log (5000 / 5837) ≤ (77389527 / 500000000) := by
  have h := checkLog_sound (w := (837 / 10837)) (n := 12)
    (lo := (154779053 / 1000000000)) (hi := (77389527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5837 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5837 / 5000) = 1/(5000 / 5837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2393 : Bounds (154779053 / 1000000000) (77389527 / 500000000) (Real.log (5837 / 5000)) := by
  have h := reflection_log_2393_neg
  have he : Real.log (5837 / 5000) = -Real.log (5000 / 5837) := by
    rw [show ((5837 / 5000) : ℝ) = ((5000 / 5837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2394_neg : (22900243 / 125000000) ≤ -Real.log (4163 / 5000) ∧
    -Real.log (4163 / 5000) ≤ (36640389 / 200000000) := by
  have h := checkLog_sound (w := (837 / 9163)) (n := 12)
    (lo := (22900243 / 125000000)) (hi := (36640389 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4163) = 1/(4163 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2394 : Bounds (-36640389 / 200000000) (-22900243 / 125000000) (Real.log (4163 / 5000)) := by
  have h := reflection_log_2394_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2395_neg : (33477 / 200000000) ≤ -Real.log (5000000 / 5000837) ∧
    -Real.log (5000000 / 5000837) ≤ (83693 / 500000000) := by
  have h := checkLog_sound (w := (837 / 10000837)) (n := 12)
    (lo := (33477 / 200000000)) (hi := (83693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000837 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000837 / 5000000) = 1/(5000000 / 5000837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2395 : Bounds (33477 / 200000000) (83693 / 500000000) (Real.log (5000837 / 5000000)) := by
  have h := reflection_log_2395_neg
  have he : Real.log (5000837 / 5000000) = -Real.log (5000000 / 5000837) := by
    rw [show ((5000837 / 5000000) : ℝ) = ((5000000 / 5000837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2396_neg : (83707 / 500000000) ≤ -Real.log (4999163 / 5000000) ∧
    -Real.log (4999163 / 5000000) ≤ (33483 / 200000000) := by
  have h := checkLog_sound (w := (837 / 9999163)) (n := 12)
    (lo := (83707 / 500000000)) (hi := (33483 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999163) = 1/(4999163 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2396 : Bounds (-33483 / 200000000) (-83707 / 500000000) (Real.log (4999163 / 5000000)) := by
  have h := reflection_log_2396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2397_neg : (40325261 / 500000000) ≤ -Real.log (125000 / 135499) ∧
    -Real.log (125000 / 135499) ≤ (80650523 / 1000000000) := by
  have h := checkLog_sound (w := (10499 / 260499)) (n := 12)
    (lo := (40325261 / 500000000)) (hi := (80650523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135499 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135499 / 125000) = 1/(125000 / 135499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2397 : Bounds (40325261 / 500000000) (80650523 / 1000000000) (Real.log (135499 / 125000)) := by
  have h := reflection_log_2397_neg
  have he : Real.log (135499 / 125000) = -Real.log (125000 / 135499) := by
    rw [show ((135499 / 125000) : ℝ) = ((125000 / 135499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2398_neg : (4386509 / 50000000) ≤ -Real.log (114501 / 125000) ∧
    -Real.log (114501 / 125000) ≤ (87730181 / 1000000000) := by
  have h := checkLog_sound (w := (10499 / 239501)) (n := 12)
    (lo := (4386509 / 50000000)) (hi := (87730181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114501) = 1/(114501 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2398 : Bounds (-87730181 / 1000000000) (-4386509 / 50000000) (Real.log (114501 / 125000)) := by
  have h := reflection_log_2398_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2399_neg : (80851611 / 1000000000) ≤ -Real.log (100000 / 108421) ∧
    -Real.log (100000 / 108421) ≤ (20212903 / 250000000) := by
  have h := checkLog_sound (w := (8421 / 208421)) (n := 12)
    (lo := (80851611 / 1000000000)) (hi := (20212903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108421 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108421 / 100000) = 1/(100000 / 108421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2399 : Bounds (80851611 / 1000000000) (20212903 / 250000000) (Real.log (108421 / 100000)) := by
  have h := reflection_log_2399_neg
  have he : Real.log (108421 / 100000) = -Real.log (100000 / 108421) := by
    rw [show ((108421 / 100000) : ℝ) = ((100000 / 108421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2400_neg : (43984099 / 500000000) ≤ -Real.log (91579 / 100000) ∧
    -Real.log (91579 / 100000) ≤ (87968199 / 1000000000) := by
  have h := checkLog_sound (w := (8421 / 191579)) (n := 12)
    (lo := (43984099 / 500000000)) (hi := (87968199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 91579) = 1/(91579 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2400 : Bounds (-87968199 / 1000000000) (-43984099 / 500000000) (Real.log (91579 / 100000)) := by
  have h := reflection_log_2400_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2401_neg : (7116587 / 1000000000) ≤ -Real.log (9929086759 / 10000000000) ∧
    -Real.log (9929086759 / 10000000000) ≤ (1779147 / 250000000) := by
  have h := checkLog_sound (w := (70913241 / 19929086759)) (n := 12)
    (lo := (7116587 / 1000000000)) (hi := (1779147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9929086759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9929086759) = 1/(9929086759 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2401 : Bounds (-1779147 / 250000000) (-7116587 / 1000000000) (Real.log (9929086759 / 10000000000)) := by
  have h := reflection_log_2401_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2402_neg : (7079657 / 1000000000) ≤ -Real.log (15514770999 / 15625000000) ∧
    -Real.log (15514770999 / 15625000000) ≤ (3539829 / 500000000) := by
  have h := checkLog_sound (w := (110229001 / 31139770999)) (n := 12)
    (lo := (7079657 / 1000000000)) (hi := (3539829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15514770999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15514770999) = 1/(15514770999 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2402 : Bounds (-3539829 / 500000000) (-7079657 / 1000000000) (Real.log (15514770999 / 15625000000)) := by
  have h := reflection_log_2402_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2403_neg : (168380703 / 1000000000) ≤ -Real.log (500000000000 / 591693522327) ∧
    -Real.log (500000000000 / 591693522327) ≤ (5261897 / 31250000) := by
  have h := checkLog_sound (w := (91693522327 / 1091693522327)) (n := 12)
    (lo := (168380703 / 1000000000)) (hi := (5261897 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591693522327 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591693522327 / 500000000000) = 1/(500000000000 / 591693522327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2403 : Bounds (168380703 / 1000000000) (5261897 / 31250000) (Real.log (591693522327 / 500000000000)) := by
  have h := reflection_log_2403_neg
  have he : Real.log (591693522327 / 500000000000) = -Real.log (500000000000 / 591693522327) := by
    rw [show ((591693522327 / 500000000000) : ℝ) = ((500000000000 / 591693522327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2404_neg : (168819809 / 1000000000) ≤ -Real.log (50000000000 / 59195339543) ∧
    -Real.log (50000000000 / 59195339543) ≤ (16881981 / 100000000) := by
  have h := checkLog_sound (w := (9195339543 / 109195339543)) (n := 12)
    (lo := (168819809 / 1000000000)) (hi := (16881981 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59195339543 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59195339543 / 50000000000) = 1/(50000000000 / 59195339543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2404 : Bounds (168819809 / 1000000000) (16881981 / 100000000) (Real.log (59195339543 / 50000000000)) := by
  have h := reflection_log_2404_neg
  have he : Real.log (59195339543 / 50000000000) = -Real.log (50000000000 / 59195339543) := by
    rw [show ((59195339543 / 50000000000) : ℝ) = ((50000000000 / 59195339543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2405_neg : (67555047 / 200000000) ≤ -Real.log (500000000000 / 700912693647) ∧
    -Real.log (500000000000 / 700912693647) ≤ (84443809 / 250000000) := by
  have h := checkLog_sound (w := (200912693647 / 1200912693647)) (n := 12)
    (lo := (67555047 / 200000000)) (hi := (84443809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700912693647 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700912693647 / 500000000000) = 1/(500000000000 / 700912693647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2405 : Bounds (67555047 / 200000000) (84443809 / 250000000) (Real.log (700912693647 / 500000000000)) := by
  have h := reflection_log_2405_neg
  have he : Real.log (700912693647 / 500000000000) = -Real.log (500000000000 / 700912693647) := by
    rw [show ((700912693647 / 500000000000) : ℝ) = ((500000000000 / 700912693647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2406_neg : (168990499 / 500000000) ≤ -Real.log (500000000000 / 701056930099) ∧
    -Real.log (500000000000 / 701056930099) ≤ (337980999 / 1000000000) := by
  have h := checkLog_sound (w := (201056930099 / 1201056930099)) (n := 12)
    (lo := (168990499 / 500000000)) (hi := (337980999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701056930099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701056930099 / 500000000000) = 1/(500000000000 / 701056930099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2406 : Bounds (168990499 / 500000000) (337980999 / 1000000000) (Real.log (701056930099 / 500000000000)) := by
  have h := reflection_log_2406_neg
  have he : Real.log (701056930099 / 500000000000) = -Real.log (500000000000 / 701056930099) := by
    rw [show ((701056930099 / 500000000000) : ℝ) = ((500000000000 / 701056930099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2407_neg : (15486471 / 100000000) ≤ -Real.log (400 / 467) ∧
    -Real.log (400 / 467) ≤ (154864711 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 867)) (n := 12)
    (lo := (15486471 / 100000000)) (hi := (154864711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((467 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(467 / 400) = 1/(400 / 467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2407 : Bounds (15486471 / 100000000) (154864711 / 1000000000) (Real.log (467 / 400)) := by
  have h := reflection_log_2407_neg
  have he : Real.log (467 / 400) = -Real.log (400 / 467) := by
    rw [show ((467 / 400) : ℝ) = ((400 / 467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2408_neg : (183322057 / 1000000000) ≤ -Real.log (333 / 400) ∧
    -Real.log (333 / 400) ≤ (91661029 / 500000000) := by
  have h := checkLog_sound (w := (67 / 733)) (n := 12)
    (lo := (183322057 / 1000000000)) (hi := (91661029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 333) = 1/(333 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2408 : Bounds (-91661029 / 500000000) (-183322057 / 1000000000) (Real.log (333 / 400)) := by
  have h := reflection_log_2408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2409_neg : (33497 / 200000000) ≤ -Real.log (400000 / 400067) ∧
    -Real.log (400000 / 400067) ≤ (83743 / 500000000) := by
  have h := checkLog_sound (w := (67 / 800067)) (n := 12)
    (lo := (33497 / 200000000)) (hi := (83743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400067 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400067 / 400000) = 1/(400000 / 400067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2409 : Bounds (33497 / 200000000) (83743 / 500000000) (Real.log (400067 / 400000)) := by
  have h := reflection_log_2409_neg
  have he : Real.log (400067 / 400000) = -Real.log (400000 / 400067) := by
    rw [show ((400067 / 400000) : ℝ) = ((400000 / 400067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2410_neg : (83757 / 500000000) ≤ -Real.log (399933 / 400000) ∧
    -Real.log (399933 / 400000) ≤ (33503 / 200000000) := by
  have h := checkLog_sound (w := (67 / 799933)) (n := 12)
    (lo := (83757 / 500000000)) (hi := (33503 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399933) = 1/(399933 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2410 : Bounds (-33503 / 200000000) (-83757 / 500000000) (Real.log (399933 / 400000)) := by
  have h := reflection_log_2410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2411_neg : (8069757 / 100000000) ≤ -Real.log (1000000 / 1084043) ∧
    -Real.log (1000000 / 1084043) ≤ (80697571 / 1000000000) := by
  have h := checkLog_sound (w := (84043 / 2084043)) (n := 12)
    (lo := (8069757 / 100000000)) (hi := (80697571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084043 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084043 / 1000000) = 1/(1000000 / 1084043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2411 : Bounds (8069757 / 100000000) (80697571 / 1000000000) (Real.log (1084043 / 1000000)) := by
  have h := reflection_log_2411_neg
  have he : Real.log (1084043 / 1000000) = -Real.log (1000000 / 1084043) := by
    rw [show ((1084043 / 1000000) : ℝ) = ((1000000 / 1084043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2412_neg : (43892929 / 500000000) ≤ -Real.log (915957 / 1000000) ∧
    -Real.log (915957 / 1000000) ≤ (87785859 / 1000000000) := by
  have h := checkLog_sound (w := (84043 / 1915957)) (n := 12)
    (lo := (43892929 / 500000000)) (hi := (87785859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915957) = 1/(915957 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2412 : Bounds (-87785859 / 1000000000) (-43892929 / 500000000) (Real.log (915957 / 1000000)) := by
  have h := reflection_log_2412_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2413_neg : (10112331 / 125000000) ≤ -Real.log (1000000 / 1084261) ∧
    -Real.log (1000000 / 1084261) ≤ (80898649 / 1000000000) := by
  have h := checkLog_sound (w := (84261 / 2084261)) (n := 12)
    (lo := (10112331 / 125000000)) (hi := (80898649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084261 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084261 / 1000000) = 1/(1000000 / 1084261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2413 : Bounds (10112331 / 125000000) (80898649 / 1000000000) (Real.log (1084261 / 1000000)) := by
  have h := reflection_log_2413_neg
  have he : Real.log (1084261 / 1000000) = -Real.log (1000000 / 1084261) := by
    rw [show ((1084261 / 1000000) : ℝ) = ((1000000 / 1084261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2414_neg : (88023889 / 1000000000) ≤ -Real.log (915739 / 1000000) ∧
    -Real.log (915739 / 1000000) ≤ (8802389 / 100000000) := by
  have h := checkLog_sound (w := (84261 / 1915739)) (n := 12)
    (lo := (88023889 / 1000000000)) (hi := (8802389 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915739) = 1/(915739 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2414 : Bounds (-8802389 / 100000000) (-88023889 / 1000000000) (Real.log (915739 / 1000000)) := by
  have h := reflection_log_2414_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2415_neg : (178131 / 25000000) ≤ -Real.log (992900083879 / 1000000000000) ∧
    -Real.log (992900083879 / 1000000000000) ≤ (7125241 / 1000000000) := by
  have h := checkLog_sound (w := (7099916121 / 1992900083879)) (n := 12)
    (lo := (178131 / 25000000)) (hi := (7125241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992900083879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992900083879) = 1/(992900083879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2415 : Bounds (-7125241 / 1000000000) (-178131 / 25000000) (Real.log (992900083879 / 1000000000000)) := by
  have h := reflection_log_2415_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2416_neg : (221509 / 31250000) ≤ -Real.log (992936774151 / 1000000000000) ∧
    -Real.log (992936774151 / 1000000000000) ≤ (7088289 / 1000000000) := by
  have h := checkLog_sound (w := (7063225849 / 1992936774151)) (n := 12)
    (lo := (221509 / 31250000)) (hi := (7088289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992936774151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992936774151) = 1/(992936774151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2416 : Bounds (-7088289 / 1000000000) (-221509 / 31250000) (Real.log (992936774151 / 1000000000000)) := by
  have h := reflection_log_2416_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2417_neg : (42120857 / 250000000) ≤ -Real.log (500000000000 / 591754307243) ∧
    -Real.log (500000000000 / 591754307243) ≤ (168483429 / 1000000000) := by
  have h := checkLog_sound (w := (91754307243 / 1091754307243)) (n := 12)
    (lo := (42120857 / 250000000)) (hi := (168483429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591754307243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591754307243 / 500000000000) = 1/(500000000000 / 591754307243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2417 : Bounds (42120857 / 250000000) (168483429 / 1000000000) (Real.log (591754307243 / 500000000000)) := by
  have h := reflection_log_2417_neg
  have he : Real.log (591754307243 / 500000000000) = -Real.log (500000000000 / 591754307243) := by
    rw [show ((591754307243 / 500000000000) : ℝ) = ((500000000000 / 591754307243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2418_neg : (84461269 / 500000000) ≤ -Real.log (500000000000 / 592014209289) ∧
    -Real.log (500000000000 / 592014209289) ≤ (168922539 / 1000000000) := by
  have h := checkLog_sound (w := (92014209289 / 1092014209289)) (n := 12)
    (lo := (84461269 / 500000000)) (hi := (168922539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592014209289 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592014209289 / 500000000000) = 1/(500000000000 / 592014209289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2418 : Bounds (84461269 / 500000000) (168922539 / 1000000000) (Real.log (592014209289 / 500000000000)) := by
  have h := reflection_log_2418_neg
  have he : Real.log (592014209289 / 500000000000) = -Real.log (500000000000 / 592014209289) := by
    rw [show ((592014209289 / 500000000000) : ℝ) = ((500000000000 / 592014209289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2419_neg : (168990499 / 500000000) ≤ -Real.log (250000000000 / 350528465049) ∧
    -Real.log (250000000000 / 350528465049) ≤ (337980999 / 1000000000) := by
  have h := checkLog_sound (w := (100528465049 / 600528465049)) (n := 12)
    (lo := (168990499 / 500000000)) (hi := (337980999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350528465049 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350528465049 / 250000000000) = 1/(250000000000 / 350528465049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2419 : Bounds (168990499 / 500000000) (337980999 / 1000000000) (Real.log (350528465049 / 250000000000)) := by
  have h := reflection_log_2419_neg
  have he : Real.log (350528465049 / 250000000000) = -Real.log (250000000000 / 350528465049) := by
    rw [show ((350528465049 / 250000000000) : ℝ) = ((250000000000 / 350528465049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2420_neg : (338186767 / 1000000000) ≤ -Real.log (250000000000 / 350600600601) ∧
    -Real.log (250000000000 / 350600600601) ≤ (21136673 / 62500000) := by
  have h := checkLog_sound (w := (100600600601 / 600600600601)) (n := 12)
    (lo := (338186767 / 1000000000)) (hi := (21136673 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350600600601 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350600600601 / 250000000000) = 1/(250000000000 / 350600600601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2420 : Bounds (338186767 / 1000000000) (21136673 / 62500000) (Real.log (350600600601 / 250000000000)) := by
  have h := reflection_log_2420_neg
  have he : Real.log (350600600601 / 250000000000) = -Real.log (250000000000 / 350600600601) := by
    rw [show ((350600600601 / 250000000000) : ℝ) = ((250000000000 / 350600600601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2421_neg : (154950359 / 1000000000) ≤ -Real.log (2500 / 2919) ∧
    -Real.log (2500 / 2919) ≤ (3873759 / 25000000) := by
  have h := checkLog_sound (w := (419 / 5419)) (n := 12)
    (lo := (154950359 / 1000000000)) (hi := (3873759 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2919 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2919 / 2500) = 1/(2500 / 2919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2421 : Bounds (154950359 / 1000000000) (3873759 / 25000000) (Real.log (2919 / 2500)) := by
  have h := reflection_log_2421_neg
  have he : Real.log (2919 / 2500) = -Real.log (2500 / 2919) := by
    rw [show ((2919 / 2500) : ℝ) = ((2500 / 2919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2422_neg : (22930273 / 125000000) ≤ -Real.log (2081 / 2500) ∧
    -Real.log (2081 / 2500) ≤ (36688437 / 200000000) := by
  have h := checkLog_sound (w := (419 / 4581)) (n := 12)
    (lo := (22930273 / 125000000)) (hi := (36688437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2081) = 1/(2081 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2422 : Bounds (-36688437 / 200000000) (-22930273 / 125000000) (Real.log (2081 / 2500)) := by
  have h := reflection_log_2422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2423_neg : (33517 / 200000000) ≤ -Real.log (2500000 / 2500419) ∧
    -Real.log (2500000 / 2500419) ≤ (83793 / 500000000) := by
  have h := checkLog_sound (w := (419 / 5000419)) (n := 12)
    (lo := (33517 / 200000000)) (hi := (83793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500419 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500419 / 2500000) = 1/(2500000 / 2500419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2423 : Bounds (33517 / 200000000) (83793 / 500000000) (Real.log (2500419 / 2500000)) := by
  have h := reflection_log_2423_neg
  have he : Real.log (2500419 / 2500000) = -Real.log (2500000 / 2500419) := by
    rw [show ((2500419 / 2500000) : ℝ) = ((2500000 / 2500419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2424_neg : (83807 / 500000000) ≤ -Real.log (2499581 / 2500000) ∧
    -Real.log (2499581 / 2500000) ≤ (33523 / 200000000) := by
  have h := checkLog_sound (w := (419 / 4999581)) (n := 12)
    (lo := (83807 / 500000000)) (hi := (33523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499581) = 1/(2499581 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2424 : Bounds (-33523 / 200000000) (-83807 / 500000000) (Real.log (2499581 / 2500000)) := by
  have h := reflection_log_2424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2425_neg : (20185923 / 250000000) ≤ -Real.log (1000000 / 1084093) ∧
    -Real.log (1000000 / 1084093) ≤ (80743693 / 1000000000) := by
  have h := checkLog_sound (w := (84093 / 2084093)) (n := 12)
    (lo := (20185923 / 250000000)) (hi := (80743693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084093 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084093 / 1000000) = 1/(1000000 / 1084093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2425 : Bounds (20185923 / 250000000) (80743693 / 1000000000) (Real.log (1084093 / 1000000)) := by
  have h := reflection_log_2425_neg
  have he : Real.log (1084093 / 1000000) = -Real.log (1000000 / 1084093) := by
    rw [show ((1084093 / 1000000) : ℝ) = ((1000000 / 1084093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2426_neg : (87840447 / 1000000000) ≤ -Real.log (915907 / 1000000) ∧
    -Real.log (915907 / 1000000) ≤ (1372507 / 15625000) := by
  have h := checkLog_sound (w := (84093 / 1915907)) (n := 12)
    (lo := (87840447 / 1000000000)) (hi := (1372507 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915907) = 1/(915907 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2426 : Bounds (-1372507 / 15625000) (-87840447 / 1000000000) (Real.log (915907 / 1000000)) := by
  have h := reflection_log_2426_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2427_neg : (20236421 / 250000000) ≤ -Real.log (125000 / 135539) ∧
    -Real.log (125000 / 135539) ≤ (16189137 / 200000000) := by
  have h := checkLog_sound (w := (10539 / 260539)) (n := 12)
    (lo := (20236421 / 250000000)) (hi := (16189137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135539 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135539 / 125000) = 1/(125000 / 135539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2427 : Bounds (20236421 / 250000000) (16189137 / 200000000) (Real.log (135539 / 125000)) := by
  have h := reflection_log_2427_neg
  have he : Real.log (135539 / 125000) = -Real.log (125000 / 135539) := by
    rw [show ((135539 / 125000) : ℝ) = ((125000 / 135539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2428_neg : (88079583 / 1000000000) ≤ -Real.log (114461 / 125000) ∧
    -Real.log (114461 / 125000) ≤ (2752487 / 31250000) := by
  have h := checkLog_sound (w := (10539 / 239461)) (n := 12)
    (lo := (88079583 / 1000000000)) (hi := (2752487 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114461) = 1/(114461 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2428 : Bounds (-2752487 / 31250000) (-88079583 / 1000000000) (Real.log (114461 / 125000)) := by
  have h := reflection_log_2428_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2429_neg : (7133899 / 1000000000) ≤ -Real.log (15513929479 / 15625000000) ∧
    -Real.log (15513929479 / 15625000000) ≤ (71339 / 10000000) := by
  have h := checkLog_sound (w := (111070521 / 31138929479)) (n := 12)
    (lo := (7133899 / 1000000000)) (hi := (71339 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15513929479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15513929479) = 1/(15513929479 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2429 : Bounds (-71339 / 10000000) (-7133899 / 1000000000) (Real.log (15513929479 / 15625000000)) := by
  have h := reflection_log_2429_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2430_neg : (1419351 / 200000000) ≤ -Real.log (992928367351 / 1000000000000) ∧
    -Real.log (992928367351 / 1000000000000) ≤ (1774189 / 250000000) := by
  have h := checkLog_sound (w := (7071632649 / 1992928367351)) (n := 12)
    (lo := (1419351 / 200000000)) (hi := (1774189 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992928367351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992928367351) = 1/(992928367351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2430 : Bounds (-1774189 / 250000000) (-1419351 / 200000000) (Real.log (992928367351 / 1000000000000)) := by
  have h := reflection_log_2430_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2431_neg : (8429207 / 50000000) ≤ -Real.log (50000000000 / 59181390687) ∧
    -Real.log (50000000000 / 59181390687) ≤ (168584141 / 1000000000) := by
  have h := checkLog_sound (w := (9181390687 / 109181390687)) (n := 12)
    (lo := (8429207 / 50000000)) (hi := (168584141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59181390687 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59181390687 / 50000000000) = 1/(50000000000 / 59181390687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2431 : Bounds (8429207 / 50000000) (168584141 / 1000000000) (Real.log (59181390687 / 50000000000)) := by
  have h := reflection_log_2431_neg
  have he : Real.log (59181390687 / 50000000000) = -Real.log (50000000000 / 59181390687) := by
    rw [show ((59181390687 / 50000000000) : ℝ) = ((50000000000 / 59181390687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
