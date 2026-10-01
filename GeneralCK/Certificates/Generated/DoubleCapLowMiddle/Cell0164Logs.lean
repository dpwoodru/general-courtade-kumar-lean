import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0164
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

theorem reflection_log_1_neg : (128510531 / 200000000) ≤ -Real.log (12800 / 24337) ∧
    -Real.log (12800 / 24337) ≤ (40159541 / 62500000) := by
  have h := checkLog_sound (w := (11537 / 37137)) (n := 12)
    (lo := (128510531 / 200000000)) (hi := (40159541 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24337 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24337 / 12800) = 1/(12800 / 24337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128510531 / 200000000) (40159541 / 62500000) (Real.log (24337 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24337 / 12800) = -Real.log (12800 / 24337) := by
    rw [show ((24337 / 12800) : ℝ) = ((12800 / 24337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (92638213 / 40000000) ≤ -Real.log (1263 / 12800) ∧
    -Real.log (1263 / 12800) ≤ (2315955329 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 2863)) (n := 12)
    (lo := (47302757 / 200000000)) (hi := (118256893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1263) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1263) = 1/(1263 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2315955329 / 1000000000) (-92638213 / 40000000) (Real.log (1263 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128354329 / 200000000) ≤ -Real.log (6400 / 12159) ∧
    -Real.log (6400 / 12159) ≤ (320885823 / 500000000) := by
  have h := checkLog_sound (w := (5759 / 18559)) (n := 12)
    (lo := (128354329 / 200000000)) (hi := (320885823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12159 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12159 / 6400) = 1/(6400 / 12159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128354329 / 200000000) (320885823 / 500000000) (Real.log (12159 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12159 / 6400) = -Real.log (6400 / 12159) := by
    rw [show ((12159 / 6400) : ℝ) = ((6400 / 12159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (230102381 / 100000000) ≤ -Real.log (641 / 6400) ∧
    -Real.log (641 / 6400) ≤ (1150511907 / 500000000) := by
  have h := checkLog_sound (w := (159 / 1441)) (n := 12)
    (lo := (22158227 / 100000000)) (hi := (221582271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 641) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 641) = 1/(641 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1150511907 / 500000000) (-230102381 / 100000000) (Real.log (641 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (589261271 / 1000000000) ≤ -Real.log (6400 / 11537) ∧
    -Real.log (6400 / 11537) ≤ (73657659 / 125000000) := by
  have h := checkLog_sound (w := (5137 / 17937)) (n := 12)
    (lo := (589261271 / 1000000000)) (hi := (73657659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11537 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11537 / 6400) = 1/(6400 / 11537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (589261271 / 1000000000) (73657659 / 125000000) (Real.log (11537 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11537 / 6400) = -Real.log (6400 / 11537) := by
    rw [show ((11537 / 6400) : ℝ) = ((6400 / 11537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (324561629 / 200000000) ≤ -Real.log (1263 / 6400) ∧
    -Real.log (1263 / 6400) ≤ (405702037 / 250000000) := by
  have h := checkLog_sound (w := (337 / 2863)) (n := 12)
    (lo := (47302757 / 200000000)) (hi := (118256893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1263) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1263) = 1/(1263 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-405702037 / 250000000) (-324561629 / 200000000) (Real.log (1263 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (293806519 / 500000000) ≤ -Real.log (3200 / 5759) ∧
    -Real.log (3200 / 5759) ≤ (587613039 / 1000000000) := by
  have h := checkLog_sound (w := (2559 / 8959)) (n := 12)
    (lo := (293806519 / 500000000)) (hi := (587613039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5759 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5759 / 3200) = 1/(3200 / 5759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (293806519 / 500000000) (587613039 / 1000000000) (Real.log (5759 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5759 / 3200) = -Real.log (3200 / 5759) := by
    rw [show ((5759 / 3200) : ℝ) = ((3200 / 5759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (160787663 / 100000000) ≤ -Real.log (641 / 3200) ∧
    -Real.log (641 / 3200) ≤ (1607876633 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 1441)) (n := 12)
    (lo := (22158227 / 100000000)) (hi := (221582271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 641) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 641) = 1/(641 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1607876633 / 1000000000) (-160787663 / 100000000) (Real.log (641 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (327013171 / 500000000) ≤ -Real.log (1000000 / 1923269) ∧
    -Real.log (1000000 / 1923269) ≤ (654026343 / 1000000000) := by
  have h := checkLog_sound (w := (923269 / 2923269)) (n := 12)
    (lo := (327013171 / 500000000)) (hi := (654026343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1923269 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1923269 / 1000000) = 1/(1000000 / 1923269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (327013171 / 500000000) (654026343 / 1000000000) (Real.log (1923269 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1923269 / 1000000) = -Real.log (1000000 / 1923269) := by
    rw [show ((1923269 / 1000000) : ℝ) = ((1000000 / 1923269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1283724739 / 500000000) ≤ -Real.log (76731 / 1000000) ∧
    -Real.log (76731 / 1000000) ≤ (1283724741 / 500000000) := by
  have h := checkLog_sound (w := (48269 / 201731)) (n := 12)
    (lo := (244003969 / 500000000)) (hi := (488007939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 76731) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 76731) = 1/(76731 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1283724741 / 500000000) (-1283724739 / 500000000) (Real.log (76731 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (13091079 / 20000000) ≤ -Real.log (250000 / 481071) ∧
    -Real.log (250000 / 481071) ≤ (654553951 / 1000000000) := by
  have h := checkLog_sound (w := (231071 / 731071)) (n := 12)
    (lo := (13091079 / 20000000)) (hi := (654553951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481071 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481071 / 250000) = 1/(250000 / 481071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (13091079 / 20000000) (654553951 / 1000000000) (Real.log (481071 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (481071 / 250000) = -Real.log (250000 / 481071) := by
    rw [show ((481071 / 250000) : ℝ) = ((250000 / 481071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1290382889 / 500000000) ≤ -Real.log (18929 / 250000) ∧
    -Real.log (18929 / 250000) ≤ (1290382891 / 500000000) := by
  have h := checkLog_sound (w := (12321 / 50179)) (n := 12)
    (lo := (250662119 / 500000000)) (hi := (501324239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18929) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 18929) = 1/(18929 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1290382891 / 500000000) (-1290382889 / 500000000) (Real.log (18929 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (326395351 / 500000000) ≤ -Real.log (500000 / 960447) ∧
    -Real.log (500000 / 960447) ≤ (652790703 / 1000000000) := by
  have h := checkLog_sound (w := (460447 / 1460447)) (n := 12)
    (lo := (326395351 / 500000000)) (hi := (652790703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960447 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(960447 / 500000) = 1/(500000 / 960447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (326395351 / 500000000) (652790703 / 1000000000) (Real.log (960447 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (960447 / 500000) = -Real.log (500000 / 960447) := by
    rw [show ((960447 / 500000) : ℝ) = ((500000 / 960447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (317120819 / 125000000) ≤ -Real.log (39553 / 500000) ∧
    -Real.log (39553 / 500000) ≤ (634241639 / 250000000) := by
  have h := checkLog_sound (w := (22947 / 102053)) (n := 12)
    (lo := (114381253 / 250000000)) (hi := (457525013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 39553) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 39553) = 1/(39553 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-634241639 / 250000000) (-317120819 / 125000000) (Real.log (39553 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (653361107 / 1000000000) ≤ -Real.log (100000 / 192199) ∧
    -Real.log (100000 / 192199) ≤ (163340277 / 250000000) := by
  have h := checkLog_sound (w := (92199 / 292199)) (n := 12)
    (lo := (653361107 / 1000000000)) (hi := (163340277 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192199 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192199 / 100000) = 1/(100000 / 192199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (653361107 / 1000000000) (163340277 / 250000000) (Real.log (192199 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (192199 / 100000) = -Real.log (100000 / 192199) := by
    rw [show ((192199 / 100000) : ℝ) = ((100000 / 192199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2550918253 / 1000000000) ≤ -Real.log (7801 / 100000) ∧
    -Real.log (7801 / 100000) ≤ (2550918257 / 1000000000) := by
  have h := checkLog_sound (w := (4699 / 20301)) (n := 12)
    (lo := (471476713 / 1000000000)) (hi := (235738357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7801) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 7801) = 1/(7801 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2550918257 / 1000000000) (-2550918253 / 1000000000) (Real.log (7801 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (161073791 / 50000000) ≤ -Real.log (250000000000 / 6266271129009) ∧
    -Real.log (250000000000 / 6266271129009) ≤ (128859033 / 40000000) := by
  have h := checkLog_sound (w := (2266271129009 / 10266271129009)) (n := 12)
    (lo := (4488871 / 10000000)) (hi := (448887101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6266271129009 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6266271129009 / 4000000000000) = 1/(250000000000 / 6266271129009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (161073791 / 50000000) (128859033 / 40000000) (Real.log (6266271129009 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6266271129009 / 250000000000) = -Real.log (250000000000 / 6266271129009) := by
    rw [show ((6266271129009 / 250000000000) : ℝ) = ((250000000000 / 6266271129009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (202207483 / 62500000) ≤ -Real.log (500000000000 / 12707248137779) ∧
    -Real.log (500000000000 / 12707248137779) ≤ (3235319733 / 1000000000) := by
  have h := checkLog_sound (w := (4707248137779 / 20707248137779)) (n := 12)
    (lo := (1807543 / 3906250)) (hi := (462731009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12707248137779 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12707248137779 / 8000000000000) = 1/(500000000000 / 12707248137779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (202207483 / 62500000) (3235319733 / 1000000000) (Real.log (12707248137779 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12707248137779 / 500000000000) = -Real.log (500000000000 / 12707248137779) := by
    rw [show ((12707248137779 / 500000000000) : ℝ) = ((500000000000 / 12707248137779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1594878627 / 500000000) ≤ -Real.log (500000000000 / 12141266149217) ∧
    -Real.log (500000000000 / 12141266149217) ≤ (3189757259 / 1000000000) := by
  have h := checkLog_sound (w := (4141266149217 / 20141266149217)) (n := 12)
    (lo := (208584267 / 500000000)) (hi := (83433707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12141266149217 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12141266149217 / 8000000000000) = 1/(500000000000 / 12141266149217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1594878627 / 500000000) (3189757259 / 1000000000) (Real.log (12141266149217 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (12141266149217 / 500000000000) = -Real.log (500000000000 / 12141266149217) := by
    rw [show ((12141266149217 / 500000000000) : ℝ) = ((500000000000 / 12141266149217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (10013373 / 3125000) ≤ -Real.log (250000000000 / 6159434687861) ∧
    -Real.log (250000000000 / 6159434687861) ≤ (640855873 / 200000000) := by
  have h := checkLog_sound (w := (2159434687861 / 10159434687861)) (n := 12)
    (lo := (5396133 / 12500000)) (hi := (431690641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6159434687861 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6159434687861 / 4000000000000) = 1/(250000000000 / 6159434687861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (10013373 / 3125000) (640855873 / 200000000) (Real.log (6159434687861 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6159434687861 / 250000000000) = -Real.log (250000000000 / 6159434687861) := by
    rw [show ((6159434687861 / 250000000000) : ℝ) = ((250000000000 / 6159434687861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0164
