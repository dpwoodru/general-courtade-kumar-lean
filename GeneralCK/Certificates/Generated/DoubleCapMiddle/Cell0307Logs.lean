import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0307
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

theorem reflection_log_1_neg : (111141903 / 500000000) ≤ -Real.log (10240 / 12789) ∧
    -Real.log (10240 / 12789) ≤ (222283807 / 1000000000) := by
  have h := checkLog_sound (w := (2549 / 23029)) (n := 12)
    (lo := (111141903 / 500000000)) (hi := (222283807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12789 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12789 / 10240) = 1/(10240 / 12789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (111141903 / 500000000) (222283807 / 1000000000) (Real.log (12789 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12789 / 10240) = -Real.log (10240 / 12789) := by
    rw [show ((12789 / 10240) : ℝ) = ((10240 / 12789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (57250161 / 200000000) ≤ -Real.log (7691 / 10240) ∧
    -Real.log (7691 / 10240) ≤ (143125403 / 500000000) := by
  have h := checkLog_sound (w := (2549 / 17931)) (n := 12)
    (lo := (57250161 / 200000000)) (hi := (143125403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7691) = 1/(7691 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-143125403 / 500000000) (-57250161 / 200000000) (Real.log (7691 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (111024601 / 500000000) ≤ -Real.log (5120 / 6393) ∧
    -Real.log (5120 / 6393) ≤ (222049203 / 1000000000) := by
  have h := checkLog_sound (w := (1273 / 11513)) (n := 12)
    (lo := (111024601 / 500000000)) (hi := (222049203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6393 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6393 / 5120) = 1/(5120 / 6393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (111024601 / 500000000) (222049203 / 1000000000) (Real.log (6393 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6393 / 5120) = -Real.log (5120 / 6393) := by
    rw [show ((6393 / 5120) : ℝ) = ((5120 / 6393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (57172163 / 200000000) ≤ -Real.log (3847 / 5120) ∧
    -Real.log (3847 / 5120) ≤ (17866301 / 62500000) := by
  have h := checkLog_sound (w := (1273 / 8967)) (n := 12)
    (lo := (57172163 / 200000000)) (hi := (17866301 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3847) = 1/(3847 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-17866301 / 62500000) (-57172163 / 200000000) (Real.log (3847 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (404031789 / 1000000000) ≤ -Real.log (5120 / 7669) ∧
    -Real.log (5120 / 7669) ≤ (40403179 / 100000000) := by
  have h := checkLog_sound (w := (2549 / 12789)) (n := 12)
    (lo := (404031789 / 1000000000)) (hi := (40403179 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7669 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7669 / 5120) = 1/(5120 / 7669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (404031789 / 1000000000) (40403179 / 100000000) (Real.log (7669 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7669 / 5120) = -Real.log (5120 / 7669) := by
    rw [show ((7669 / 5120) : ℝ) = ((5120 / 7669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (68885951 / 100000000) ≤ -Real.log (2571 / 5120) ∧
    -Real.log (2571 / 5120) ≤ (688859511 / 1000000000) := by
  have h := checkLog_sound (w := (2549 / 7691)) (n := 12)
    (lo := (68885951 / 100000000)) (hi := (688859511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2571) = 1/(2571 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-688859511 / 1000000000) (-68885951 / 100000000) (Real.log (2571 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (403640527 / 1000000000) ≤ -Real.log (2560 / 3833) ∧
    -Real.log (2560 / 3833) ≤ (25227533 / 62500000) := by
  have h := checkLog_sound (w := (1273 / 6393)) (n := 12)
    (lo := (403640527 / 1000000000)) (hi := (25227533 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3833 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3833 / 2560) = 1/(2560 / 3833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (403640527 / 1000000000) (25227533 / 62500000) (Real.log (3833 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3833 / 2560) = -Real.log (2560 / 3833) := by
    rw [show ((3833 / 2560) : ℝ) = ((2560 / 3833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (687693329 / 1000000000) ≤ -Real.log (1287 / 2560) ∧
    -Real.log (1287 / 2560) ≤ (68769333 / 100000000) := by
  have h := checkLog_sound (w := (1273 / 3847)) (n := 12)
    (lo := (687693329 / 1000000000)) (hi := (68769333 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1287) = 1/(1287 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-68769333 / 100000000) (-687693329 / 1000000000) (Real.log (1287 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (38037159 / 125000000) ≤ -Real.log (125000 / 169459) ∧
    -Real.log (125000 / 169459) ≤ (304297273 / 1000000000) := by
  have h := checkLog_sound (w := (44459 / 294459)) (n := 12)
    (lo := (38037159 / 125000000)) (hi := (304297273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169459 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169459 / 125000) = 1/(125000 / 169459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (38037159 / 125000000) (304297273 / 1000000000) (Real.log (169459 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (169459 / 125000) = -Real.log (125000 / 169459) := by
    rw [show ((169459 / 125000) : ℝ) = ((125000 / 169459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (87909473 / 200000000) ≤ -Real.log (80541 / 125000) ∧
    -Real.log (80541 / 125000) ≤ (219773683 / 500000000) := by
  have h := checkLog_sound (w := (44459 / 205541)) (n := 12)
    (lo := (87909473 / 200000000)) (hi := (219773683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 80541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 80541) = 1/(80541 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-219773683 / 500000000) (-87909473 / 200000000) (Real.log (80541 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (60923029 / 200000000) ≤ -Real.log (1000000 / 1356103) ∧
    -Real.log (1000000 / 1356103) ≤ (152307573 / 500000000) := by
  have h := checkLog_sound (w := (356103 / 2356103)) (n := 12)
    (lo := (60923029 / 200000000)) (hi := (152307573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1356103 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1356103 / 1000000) = 1/(1000000 / 1356103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (60923029 / 200000000) (152307573 / 500000000) (Real.log (1356103 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1356103 / 1000000) = -Real.log (1000000 / 1356103) := by
    rw [show ((1356103 / 1000000) : ℝ) = ((1000000 / 1356103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (440216503 / 1000000000) ≤ -Real.log (643897 / 1000000) ∧
    -Real.log (643897 / 1000000) ≤ (55027063 / 125000000) := by
  have h := checkLog_sound (w := (356103 / 1643897)) (n := 12)
    (lo := (440216503 / 1000000000)) (hi := (55027063 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 643897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 643897) = 1/(643897 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-55027063 / 125000000) (-440216503 / 1000000000) (Real.log (643897 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23160287 / 100000000) ≤ -Real.log (1000000 / 1260619) ∧
    -Real.log (1000000 / 1260619) ≤ (231602871 / 1000000000) := by
  have h := checkLog_sound (w := (260619 / 2260619)) (n := 12)
    (lo := (23160287 / 100000000)) (hi := (231602871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260619 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1260619 / 1000000) = 1/(1000000 / 1260619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23160287 / 100000000) (231602871 / 1000000000) (Real.log (1260619 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1260619 / 1000000) = -Real.log (1000000 / 1260619) := by
    rw [show ((1260619 / 1000000) : ℝ) = ((1000000 / 1260619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (301941929 / 1000000000) ≤ -Real.log (739381 / 1000000) ∧
    -Real.log (739381 / 1000000) ≤ (30194193 / 100000000) := by
  have h := checkLog_sound (w := (260619 / 1739381)) (n := 12)
    (lo := (301941929 / 1000000000)) (hi := (30194193 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 739381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 739381) = 1/(739381 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-30194193 / 100000000) (-301941929 / 1000000000) (Real.log (739381 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (231871749 / 1000000000) ≤ -Real.log (500000 / 630479) ∧
    -Real.log (500000 / 630479) ≤ (927487 / 4000000) := by
  have h := checkLog_sound (w := (130479 / 1130479)) (n := 12)
    (lo := (231871749 / 1000000000)) (hi := (927487 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630479 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630479 / 500000) = 1/(500000 / 630479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (231871749 / 1000000000) (927487 / 4000000) (Real.log (630479 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (630479 / 500000) = -Real.log (500000 / 630479) := by
    rw [show ((630479 / 500000) : ℝ) = ((500000 / 630479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (151200263 / 500000000) ≤ -Real.log (369521 / 500000) ∧
    -Real.log (369521 / 500000) ≤ (302400527 / 1000000000) := by
  have h := checkLog_sound (w := (130479 / 869521)) (n := 12)
    (lo := (151200263 / 500000000)) (hi := (302400527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 369521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 369521) = 1/(369521 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-302400527 / 1000000000) (-151200263 / 500000000) (Real.log (369521 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (743844637 / 1000000000) ≤ -Real.log (500000000000 / 1052004569101) ∧
    -Real.log (500000000000 / 1052004569101) ≤ (743844639 / 1000000000) := by
  have h := checkLog_sound (w := (52004569101 / 2052004569101)) (n := 12)
    (lo := (50697457 / 1000000000)) (hi := (25348729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1052004569101 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1052004569101 / 1000000000000) = 1/(500000000000 / 1052004569101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (743844637 / 1000000000) (743844639 / 1000000000) (Real.log (1052004569101 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1052004569101 / 500000000000) = -Real.log (500000000000 / 1052004569101) := by
    rw [show ((1052004569101 / 500000000000) : ℝ) = ((500000000000 / 1052004569101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (23275989 / 31250000) ≤ -Real.log (250000000000 / 526521710771) ∧
    -Real.log (250000000000 / 526521710771) ≤ (14896633 / 20000000) := by
  have h := checkLog_sound (w := (26521710771 / 1026521710771)) (n := 12)
    (lo := (12921117 / 250000000)) (hi := (51684469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((526521710771 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(526521710771 / 500000000000) = 1/(250000000000 / 526521710771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (23275989 / 31250000) (14896633 / 20000000) (Real.log (526521710771 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (526521710771 / 250000000000) = -Real.log (250000000000 / 526521710771) := by
    rw [show ((526521710771 / 250000000000) : ℝ) = ((250000000000 / 526521710771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (533544799 / 1000000000) ≤ -Real.log (12500000000 / 21312067121) ∧
    -Real.log (12500000000 / 21312067121) ≤ (666931 / 1250000) := by
  have h := checkLog_sound (w := (8812067121 / 33812067121)) (n := 12)
    (lo := (533544799 / 1000000000)) (hi := (666931 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21312067121 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21312067121 / 12500000000) = 1/(12500000000 / 21312067121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (533544799 / 1000000000) (666931 / 1250000) (Real.log (21312067121 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (21312067121 / 12500000000) = -Real.log (12500000000 / 21312067121) := by
    rw [show ((21312067121 / 12500000000) : ℝ) = ((12500000000 / 21312067121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (21370891 / 40000000) ≤ -Real.log (250000000000 / 426551535637) ∧
    -Real.log (250000000000 / 426551535637) ≤ (133568069 / 250000000) := by
  have h := checkLog_sound (w := (176551535637 / 676551535637)) (n := 12)
    (lo := (21370891 / 40000000)) (hi := (133568069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((426551535637 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(426551535637 / 250000000000) = 1/(250000000000 / 426551535637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (21370891 / 40000000) (133568069 / 250000000) (Real.log (426551535637 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (426551535637 / 250000000000) = -Real.log (250000000000 / 426551535637) := by
    rw [show ((426551535637 / 250000000000) : ℝ) = ((250000000000 / 426551535637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0307
