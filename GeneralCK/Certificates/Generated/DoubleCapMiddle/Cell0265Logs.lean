import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0265
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

theorem reflection_log_1_neg : (236028927 / 1000000000) ≤ -Real.log (5120 / 6483) ∧
    -Real.log (5120 / 6483) ≤ (460994 / 1953125) := by
  have h := checkLog_sound (w := (1363 / 11603)) (n := 12)
    (lo := (236028927 / 1000000000)) (hi := (460994 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6483 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6483 / 5120) = 1/(5120 / 6483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (236028927 / 1000000000) (460994 / 1953125) (Real.log (6483 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6483 / 5120) = -Real.log (5120 / 6483) := by
    rw [show ((6483 / 5120) : ℝ) = ((5120 / 6483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (38691709 / 125000000) ≤ -Real.log (3757 / 5120) ∧
    -Real.log (3757 / 5120) ≤ (309533673 / 1000000000) := by
  have h := checkLog_sound (w := (1363 / 8877)) (n := 12)
    (lo := (38691709 / 125000000)) (hi := (309533673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3757) = 1/(3757 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-309533673 / 1000000000) (-38691709 / 125000000) (Real.log (3757 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (235566071 / 1000000000) ≤ -Real.log (64 / 81) ∧
    -Real.log (64 / 81) ≤ (29445759 / 125000000) := by
  have h := checkLog_sound (w := (17 / 145)) (n := 12)
    (lo := (235566071 / 1000000000)) (hi := (29445759 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81 / 64) = 1/(64 / 81) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (235566071 / 1000000000) (29445759 / 125000000) (Real.log (81 / 64)) := by
  have h := reflection_log_3_neg
  have he : Real.log (81 / 64) = -Real.log (64 / 81) := by
    rw [show ((81 / 64) : ℝ) = ((64 / 81) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (308735481 / 1000000000) ≤ -Real.log (47 / 64) ∧
    -Real.log (47 / 64) ≤ (154367741 / 500000000) := by
  have h := checkLog_sound (w := (17 / 111)) (n := 12)
    (lo := (308735481 / 1000000000)) (hi := (154367741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 47) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 47) = 1/(47 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-154367741 / 500000000) (-308735481 / 1000000000) (Real.log (47 / 64)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (3334761 / 7812500) ≤ -Real.log (2560 / 3923) ∧
    -Real.log (2560 / 3923) ≤ (426849409 / 1000000000) := by
  have h := checkLog_sound (w := (1363 / 6483)) (n := 12)
    (lo := (3334761 / 7812500)) (hi := (426849409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3923 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3923 / 2560) = 1/(2560 / 3923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (3334761 / 7812500) (426849409 / 1000000000) (Real.log (3923 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3923 / 2560) = -Real.log (2560 / 3923) := by
    rw [show ((3923 / 2560) : ℝ) = ((2560 / 3923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (760188831 / 1000000000) ≤ -Real.log (1197 / 2560) ∧
    -Real.log (1197 / 2560) ≤ (760188833 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 2477)) (n := 12)
    (lo := (67041651 / 1000000000)) (hi := (16760413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1197) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1197) = 1/(1197 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-760188833 / 1000000000) (-760188831 / 1000000000) (Real.log (1197 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (85216879 / 200000000) ≤ -Real.log (32 / 49) ∧
    -Real.log (32 / 49) ≤ (106521099 / 250000000) := by
  have h := checkLog_sound (w := (17 / 81)) (n := 12)
    (lo := (85216879 / 200000000)) (hi := (106521099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49 / 32) = 1/(32 / 49) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (85216879 / 200000000) (106521099 / 250000000) (Real.log (49 / 32)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49 / 32) = -Real.log (32 / 49) := by
    rw [show ((49 / 32) : ℝ) = ((32 / 49) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (757685701 / 1000000000) ≤ -Real.log (15 / 32) ∧
    -Real.log (15 / 32) ≤ (757685703 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16 / 15) = 1/(15 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-757685703 / 1000000000) (-757685701 / 1000000000) (Real.log (15 / 32)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (322576131 / 1000000000) ≤ -Real.log (25000 / 34517) ∧
    -Real.log (25000 / 34517) ≤ (80644033 / 250000000) := by
  have h := checkLog_sound (w := (9517 / 59517)) (n := 12)
    (lo := (322576131 / 1000000000)) (hi := (80644033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34517 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34517 / 25000) = 1/(25000 / 34517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (322576131 / 1000000000) (80644033 / 250000000) (Real.log (34517 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (34517 / 25000) = -Real.log (25000 / 34517) := by
    rw [show ((34517 / 25000) : ℝ) = ((25000 / 34517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (479133177 / 1000000000) ≤ -Real.log (15483 / 25000) ∧
    -Real.log (15483 / 25000) ≤ (239566589 / 500000000) := by
  have h := checkLog_sound (w := (9517 / 40483)) (n := 12)
    (lo := (479133177 / 1000000000)) (hi := (239566589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 15483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 15483) = 1/(15483 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-239566589 / 500000000) (-479133177 / 1000000000) (Real.log (15483 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (64640777 / 200000000) ≤ -Real.log (1000000 / 1381547) ∧
    -Real.log (1000000 / 1381547) ≤ (161601943 / 500000000) := by
  have h := checkLog_sound (w := (381547 / 2381547)) (n := 12)
    (lo := (64640777 / 200000000)) (hi := (161601943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1381547 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1381547 / 1000000) = 1/(1000000 / 1381547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (64640777 / 200000000) (161601943 / 500000000) (Real.log (1381547 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1381547 / 1000000) = -Real.log (1000000 / 1381547) := by
    rw [show ((1381547 / 1000000) : ℝ) = ((1000000 / 1381547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1501669 / 3125000) ≤ -Real.log (618453 / 1000000) ∧
    -Real.log (618453 / 1000000) ≤ (480534081 / 1000000000) := by
  have h := checkLog_sound (w := (381547 / 1618453)) (n := 12)
    (lo := (1501669 / 3125000)) (hi := (480534081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 618453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 618453) = 1/(618453 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-480534081 / 1000000000) (-1501669 / 3125000) (Real.log (618453 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (247188149 / 1000000000) ≤ -Real.log (50000 / 64021) ∧
    -Real.log (50000 / 64021) ≤ (4943763 / 20000000) := by
  have h := checkLog_sound (w := (14021 / 114021)) (n := 12)
    (lo := (247188149 / 1000000000)) (hi := (4943763 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64021 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64021 / 50000) = 1/(50000 / 64021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (247188149 / 1000000000) (4943763 / 20000000) (Real.log (64021 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (64021 / 50000) = -Real.log (50000 / 64021) := by
    rw [show ((64021 / 50000) : ℝ) = ((50000 / 64021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (32908757 / 100000000) ≤ -Real.log (35979 / 50000) ∧
    -Real.log (35979 / 50000) ≤ (329087571 / 1000000000) := by
  have h := checkLog_sound (w := (14021 / 85979)) (n := 12)
    (lo := (32908757 / 100000000)) (hi := (329087571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 35979) = 1/(35979 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-329087571 / 1000000000) (-32908757 / 100000000) (Real.log (35979 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (4954569 / 20000000) ≤ -Real.log (125000 / 160139) ∧
    -Real.log (125000 / 160139) ≤ (247728451 / 1000000000) := by
  have h := checkLog_sound (w := (35139 / 285139)) (n := 12)
    (lo := (4954569 / 20000000)) (hi := (247728451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160139 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160139 / 125000) = 1/(125000 / 160139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (4954569 / 20000000) (247728451 / 1000000000) (Real.log (160139 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (160139 / 125000) = -Real.log (125000 / 160139) := by
    rw [show ((160139 / 125000) : ℝ) = ((125000 / 160139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (66009941 / 200000000) ≤ -Real.log (89861 / 125000) ∧
    -Real.log (89861 / 125000) ≤ (165024853 / 500000000) := by
  have h := checkLog_sound (w := (35139 / 214861)) (n := 12)
    (lo := (66009941 / 200000000)) (hi := (165024853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 89861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 89861) = 1/(89861 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-165024853 / 500000000) (-66009941 / 200000000) (Real.log (89861 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (801709307 / 1000000000) ≤ -Real.log (250000000000 / 557337079377) ∧
    -Real.log (250000000000 / 557337079377) ≤ (801709309 / 1000000000) := by
  have h := checkLog_sound (w := (57337079377 / 1057337079377)) (n := 12)
    (lo := (108562127 / 1000000000)) (hi := (6785133 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((557337079377 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(557337079377 / 500000000000) = 1/(250000000000 / 557337079377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (801709307 / 1000000000) (801709309 / 1000000000) (Real.log (557337079377 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (557337079377 / 250000000000) = -Real.log (250000000000 / 557337079377) := by
    rw [show ((557337079377 / 250000000000) : ℝ) = ((250000000000 / 557337079377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (160747593 / 200000000) ≤ -Real.log (12500000000 / 27923443657) ∧
    -Real.log (12500000000 / 27923443657) ≤ (803737967 / 1000000000) := by
  have h := checkLog_sound (w := (2923443657 / 52923443657)) (n := 12)
    (lo := (22118157 / 200000000)) (hi := (55295393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27923443657 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(27923443657 / 25000000000) = 1/(12500000000 / 27923443657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (160747593 / 200000000) (803737967 / 1000000000) (Real.log (27923443657 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (27923443657 / 12500000000) = -Real.log (12500000000 / 27923443657) := by
    rw [show ((27923443657 / 12500000000) : ℝ) = ((12500000000 / 27923443657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (576275719 / 1000000000) ≤ -Real.log (500000000000 / 889699546957) ∧
    -Real.log (500000000000 / 889699546957) ≤ (14406893 / 25000000) := by
  have h := checkLog_sound (w := (389699546957 / 1389699546957)) (n := 12)
    (lo := (576275719 / 1000000000)) (hi := (14406893 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((889699546957 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(889699546957 / 500000000000) = 1/(500000000000 / 889699546957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (576275719 / 1000000000) (14406893 / 25000000) (Real.log (889699546957 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (889699546957 / 500000000000) = -Real.log (500000000000 / 889699546957) := by
    rw [show ((889699546957 / 500000000000) : ℝ) = ((500000000000 / 889699546957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (144444539 / 250000000) ≤ -Real.log (500000000000 / 891037268671) ∧
    -Real.log (500000000000 / 891037268671) ≤ (577778157 / 1000000000) := by
  have h := checkLog_sound (w := (391037268671 / 1391037268671)) (n := 12)
    (lo := (144444539 / 250000000)) (hi := (577778157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((891037268671 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(891037268671 / 500000000000) = 1/(500000000000 / 891037268671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (144444539 / 250000000) (577778157 / 1000000000) (Real.log (891037268671 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (891037268671 / 500000000000) = -Real.log (500000000000 / 891037268671) := by
    rw [show ((891037268671 / 500000000000) : ℝ) = ((500000000000 / 891037268671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0265
