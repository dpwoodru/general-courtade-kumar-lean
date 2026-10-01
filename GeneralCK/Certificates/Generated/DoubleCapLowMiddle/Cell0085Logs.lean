import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0085
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

theorem reflection_log_1_neg : (337124513 / 500000000) ≤ -Real.log (51200 / 100483) ∧
    -Real.log (51200 / 100483) ≤ (674249027 / 1000000000) := by
  have h := checkLog_sound (w := (49283 / 151683)) (n := 12)
    (lo := (337124513 / 500000000)) (hi := (674249027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100483 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100483 / 51200) = 1/(51200 / 100483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (337124513 / 500000000) (674249027 / 1000000000) (Real.log (100483 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100483 / 51200) = -Real.log (51200 / 100483) := by
    rw [show ((100483 / 51200) : ℝ) = ((51200 / 100483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (656995613 / 200000000) ≤ -Real.log (1917 / 51200) ∧
    -Real.log (1917 / 51200) ≤ (328497807 / 100000000) := by
  have h := checkLog_sound (w := (1283 / 5117)) (n := 12)
    (lo := (102477869 / 200000000)) (hi := (256194673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1917) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1917) = 1/(1917 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-328497807 / 100000000) (-656995613 / 200000000) (Real.log (1917 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (337029961 / 500000000) ≤ -Real.log (3200 / 6279) ∧
    -Real.log (3200 / 6279) ≤ (674059923 / 1000000000) := by
  have h := checkLog_sound (w := (3079 / 9479)) (n := 12)
    (lo := (337029961 / 500000000)) (hi := (674059923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6279 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6279 / 3200) = 1/(3200 / 6279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (337029961 / 500000000) (674059923 / 1000000000) (Real.log (6279 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6279 / 3200) = -Real.log (3200 / 6279) := by
    rw [show ((6279 / 3200) : ℝ) = ((3200 / 6279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (163755777 / 50000000) ≤ -Real.log (121 / 3200) ∧
    -Real.log (121 / 3200) ≤ (655023109 / 200000000) := by
  have h := checkLog_sound (w := (79 / 321)) (n := 12)
    (lo := (25126341 / 50000000)) (hi := (502526821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 121) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 121) = 1/(121 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-655023109 / 200000000) (-163755777 / 50000000) (Real.log (121 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (327493421 / 500000000) ≤ -Real.log (25600 / 49283) ∧
    -Real.log (25600 / 49283) ≤ (654986843 / 1000000000) := by
  have h := checkLog_sound (w := (23683 / 74883)) (n := 12)
    (lo := (327493421 / 500000000)) (hi := (654986843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49283 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49283 / 25600) = 1/(25600 / 49283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (327493421 / 500000000) (654986843 / 1000000000) (Real.log (49283 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49283 / 25600) = -Real.log (25600 / 49283) := by
    rw [show ((49283 / 25600) : ℝ) = ((25600 / 49283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (518366177 / 200000000) ≤ -Real.log (1917 / 25600) ∧
    -Real.log (1917 / 25600) ≤ (2591830889 / 1000000000) := by
  have h := checkLog_sound (w := (1283 / 5117)) (n := 12)
    (lo := (102477869 / 200000000)) (hi := (256194673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1917) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1917) = 1/(1917 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2591830889 / 1000000000) (-518366177 / 200000000) (Real.log (1917 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (654601239 / 1000000000) ≤ -Real.log (1600 / 3079) ∧
    -Real.log (1600 / 3079) ≤ (16365031 / 25000000) := by
  have h := checkLog_sound (w := (1479 / 4679)) (n := 12)
    (lo := (654601239 / 1000000000)) (hi := (16365031 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3079 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3079 / 1600) = 1/(1600 / 3079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (654601239 / 1000000000) (16365031 / 25000000) (Real.log (3079 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3079 / 1600) = -Real.log (1600 / 3079) := by
    rw [show ((3079 / 1600) : ℝ) = ((1600 / 3079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (64549209 / 25000000) ≤ -Real.log (121 / 1600) ∧
    -Real.log (121 / 1600) ≤ (645492091 / 250000000) := by
  have h := checkLog_sound (w := (79 / 321)) (n := 12)
    (lo := (25126341 / 50000000)) (hi := (502526821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 121) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 121) = 1/(121 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-645492091 / 250000000) (-64549209 / 25000000) (Real.log (121 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135480679 / 200000000) ≤ -Real.log (1000000 / 1968759) ∧
    -Real.log (1000000 / 1968759) ≤ (169350849 / 250000000) := by
  have h := checkLog_sound (w := (968759 / 2968759)) (n := 12)
    (lo := (135480679 / 200000000)) (hi := (169350849 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1968759 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1968759 / 1000000) = 1/(1000000 / 1968759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135480679 / 200000000) (169350849 / 250000000) (Real.log (1968759 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1968759 / 1000000) = -Real.log (1000000 / 1968759) := by
    rw [show ((1968759 / 1000000) : ℝ) = ((1000000 / 1968759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3466023941 / 1000000000) ≤ -Real.log (31241 / 1000000) ∧
    -Real.log (31241 / 1000000) ≤ (3466023947 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 62491)) (n := 12)
    (lo := (288041 / 1000000000)) (hi := (144021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31241) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 31241) = 1/(31241 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3466023947 / 1000000000) (-3466023941 / 1000000000) (Real.log (31241 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (84693899 / 125000000) ≤ -Real.log (20000 / 39381) ∧
    -Real.log (20000 / 39381) ≤ (677551193 / 1000000000) := by
  have h := checkLog_sound (w := (19381 / 59381)) (n := 12)
    (lo := (84693899 / 125000000)) (hi := (677551193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39381 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39381 / 20000) = 1/(20000 / 39381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (84693899 / 125000000) (677551193 / 1000000000) (Real.log (39381 / 20000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (39381 / 20000) = -Real.log (20000 / 39381) := by
    rw [show ((39381 / 20000) : ℝ) = ((20000 / 39381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3475382277 / 1000000000) ≤ -Real.log (619 / 20000) ∧
    -Real.log (619 / 20000) ≤ (3475382283 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 622)) (n := 12)
    (lo := (9646377 / 1000000000)) (hi := (4823189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 619) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(625 / 619) = 1/(619 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3475382283 / 1000000000) (-3475382277 / 1000000000) (Real.log (619 / 20000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (677273863 / 1000000000) ≤ -Real.log (125000 / 246063) ∧
    -Real.log (125000 / 246063) ≤ (84659233 / 125000000) := by
  have h := checkLog_sound (w := (121063 / 371063)) (n := 12)
    (lo := (677273863 / 1000000000)) (hi := (84659233 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246063 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246063 / 125000) = 1/(125000 / 246063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (677273863 / 1000000000) (84659233 / 125000000) (Real.log (246063 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (246063 / 125000) = -Real.log (125000 / 246063) := by
    rw [show ((246063 / 125000) : ℝ) = ((125000 / 246063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3457894723 / 1000000000) ≤ -Real.log (3937 / 125000) ∧
    -Real.log (3937 / 125000) ≤ (432236841 / 125000000) := by
  have h := checkLog_sound (w := (7751 / 23499)) (n := 12)
    (lo := (685306003 / 1000000000)) (hi := (171326501 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 7874) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 7874) = 1/(3937 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-432236841 / 125000000) (-3457894723 / 1000000000) (Real.log (3937 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (84678091 / 125000000) ≤ -Real.log (1000000 / 1968801) ∧
    -Real.log (1000000 / 1968801) ≤ (677424729 / 1000000000) := by
  have h := checkLog_sound (w := (968801 / 2968801)) (n := 12)
    (lo := (84678091 / 125000000)) (hi := (677424729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1968801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1968801 / 1000000) = 1/(1000000 / 1968801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (84678091 / 125000000) (677424729 / 1000000000) (Real.log (1968801 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1968801 / 1000000) = -Real.log (1000000 / 1968801) := by
    rw [show ((1968801 / 1000000) : ℝ) = ((1000000 / 1968801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3467369233 / 1000000000) ≤ -Real.log (31199 / 1000000) ∧
    -Real.log (31199 / 1000000) ≤ (3467369239 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 62449)) (n := 12)
    (lo := (1633333 / 1000000000)) (hi := (816667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31199) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 31199) = 1/(31199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3467369239 / 1000000000) (-3467369233 / 1000000000) (Real.log (31199 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (517928417 / 125000000) ≤ -Real.log (125000000000 / 7877304663743) ∧
    -Real.log (125000000000 / 7877304663743) ≤ (2071713671 / 500000000) := by
  have h := checkLog_sound (w := (3877304663743 / 11877304663743)) (n := 12)
    (lo := (169422859 / 250000000)) (hi := (677691437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7877304663743 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7877304663743 / 4000000000000) = 1/(125000000000 / 7877304663743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (517928417 / 125000000) (2071713671 / 500000000) (Real.log (7877304663743 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7877304663743 / 125000000000) = -Real.log (125000000000 / 7877304663743) := by
    rw [show ((7877304663743 / 125000000000) : ℝ) = ((125000000000 / 7877304663743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4152933469 / 1000000000) ≤ -Real.log (250000000000 / 15905088852989) ∧
    -Real.log (250000000000 / 15905088852989) ≤ (166117339 / 40000000) := by
  have h := checkLog_sound (w := (7905088852989 / 23905088852989)) (n := 12)
    (lo := (687197569 / 1000000000)) (hi := (68719757 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15905088852989 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15905088852989 / 8000000000000) = 1/(250000000000 / 15905088852989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4152933469 / 1000000000) (166117339 / 40000000) (Real.log (15905088852989 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (15905088852989 / 250000000000) = -Real.log (250000000000 / 15905088852989) := by
    rw [show ((15905088852989 / 250000000000) : ℝ) = ((250000000000 / 15905088852989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (827033717 / 200000000) ≤ -Real.log (500000000000 / 31250063500127) ∧
    -Real.log (500000000000 / 31250063500127) ≤ (4135168591 / 1000000000) := by
  have h := checkLog_sound (w := (15250063500127 / 47250063500127)) (n := 12)
    (lo := (133886537 / 200000000)) (hi := (334716343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250063500127 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250063500127 / 16000000000000) = 1/(500000000000 / 31250063500127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (827033717 / 200000000) (4135168591 / 1000000000) (Real.log (31250063500127 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (31250063500127 / 500000000000) = -Real.log (500000000000 / 31250063500127) := by
    rw [show ((31250063500127 / 500000000000) : ℝ) = ((500000000000 / 31250063500127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4144793961 / 1000000000) ≤ -Real.log (500000000000 / 31552309368891) ∧
    -Real.log (500000000000 / 31552309368891) ≤ (4144793967 / 1000000000) := by
  have h := checkLog_sound (w := (15552309368891 / 47552309368891)) (n := 12)
    (lo := (679058061 / 1000000000)) (hi := (339529031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31552309368891 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31552309368891 / 16000000000000) = 1/(500000000000 / 31552309368891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4144793961 / 1000000000) (4144793967 / 1000000000) (Real.log (31552309368891 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (31552309368891 / 500000000000) = -Real.log (500000000000 / 31552309368891) := by
    rw [show ((31552309368891 / 500000000000) : ℝ) = ((500000000000 / 31552309368891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0085
