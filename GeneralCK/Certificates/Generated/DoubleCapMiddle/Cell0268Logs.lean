import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0268
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

theorem reflection_log_1_neg : (58659929 / 250000000) ≤ -Real.log (2560 / 3237) ∧
    -Real.log (2560 / 3237) ≤ (234639717 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 5797)) (n := 12)
    (lo := (58659929 / 250000000)) (hi := (234639717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3237 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3237 / 2560) = 1/(2560 / 3237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (58659929 / 250000000) (234639717 / 1000000000) (Real.log (3237 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3237 / 2560) = -Real.log (2560 / 3237) := by
    rw [show ((3237 / 2560) : ℝ) = ((2560 / 3237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (19196313 / 62500000) ≤ -Real.log (1883 / 2560) ∧
    -Real.log (1883 / 2560) ≤ (307141009 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 4443)) (n := 12)
    (lo := (19196313 / 62500000)) (hi := (307141009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1883) = 1/(1883 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-307141009 / 1000000000) (-19196313 / 62500000) (Real.log (1883 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (234176217 / 1000000000) ≤ -Real.log (5120 / 6471) ∧
    -Real.log (5120 / 6471) ≤ (117088109 / 500000000) := by
  have h := checkLog_sound (w := (1351 / 11591)) (n := 12)
    (lo := (234176217 / 1000000000)) (hi := (117088109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6471 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6471 / 5120) = 1/(5120 / 6471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (234176217 / 1000000000) (117088109 / 500000000) (Real.log (6471 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6471 / 5120) = -Real.log (5120 / 6471) := by
    rw [show ((6471 / 5120) : ℝ) = ((5120 / 6471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (76586181 / 250000000) ≤ -Real.log (3769 / 5120) ∧
    -Real.log (3769 / 5120) ≤ (12253789 / 40000000) := by
  have h := checkLog_sound (w := (1351 / 8889)) (n := 12)
    (lo := (76586181 / 250000000)) (hi := (12253789 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3769) = 1/(3769 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12253789 / 40000000) (-76586181 / 250000000) (Real.log (3769 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42455261 / 100000000) ≤ -Real.log (1280 / 1957) ∧
    -Real.log (1280 / 1957) ≤ (424552611 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 3237)) (n := 12)
    (lo := (42455261 / 100000000)) (hi := (424552611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1957 / 1280) = 1/(1280 / 1957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42455261 / 100000000) (424552611 / 1000000000) (Real.log (1957 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1957 / 1280) = -Real.log (1280 / 1957) := by
    rw [show ((1957 / 1280) : ℝ) = ((1280 / 1957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (752698159 / 1000000000) ≤ -Real.log (603 / 1280) ∧
    -Real.log (603 / 1280) ≤ (752698161 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 1243)) (n := 12)
    (lo := (59550979 / 1000000000)) (hi := (2977549 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 603) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 603) = 1/(603 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-752698161 / 1000000000) (-752698159 / 1000000000) (Real.log (603 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (423785837 / 1000000000) ≤ -Real.log (2560 / 3911) ∧
    -Real.log (2560 / 3911) ≤ (211892919 / 500000000) := by
  have h := checkLog_sound (w := (1351 / 6471)) (n := 12)
    (lo := (423785837 / 1000000000)) (hi := (211892919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3911 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3911 / 2560) = 1/(2560 / 3911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (423785837 / 1000000000) (211892919 / 500000000) (Real.log (3911 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3911 / 2560) = -Real.log (2560 / 3911) := by
    rw [show ((3911 / 2560) : ℝ) = ((2560 / 3911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (375106843 / 500000000) ≤ -Real.log (1209 / 2560) ∧
    -Real.log (1209 / 2560) ≤ (93776711 / 125000000) := by
  have h := checkLog_sound (w := (71 / 2489)) (n := 12)
    (lo := (28533253 / 500000000)) (hi := (57066507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1209) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1209) = 1/(1209 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-93776711 / 125000000) (-375106843 / 500000000) (Real.log (1209 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (320695579 / 1000000000) ≤ -Real.log (500000 / 689043) ∧
    -Real.log (500000 / 689043) ≤ (16034779 / 50000000) := by
  have h := checkLog_sound (w := (189043 / 1189043)) (n := 12)
    (lo := (320695579 / 1000000000)) (hi := (16034779 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689043 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689043 / 500000) = 1/(500000 / 689043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (320695579 / 1000000000) (16034779 / 50000000) (Real.log (689043 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (689043 / 500000) = -Real.log (500000 / 689043) := by
    rw [show ((689043 / 500000) : ℝ) = ((500000 / 689043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (474953459 / 1000000000) ≤ -Real.log (310957 / 500000) ∧
    -Real.log (310957 / 500000) ≤ (23747673 / 50000000) := by
  have h := checkLog_sound (w := (189043 / 810957)) (n := 12)
    (lo := (474953459 / 1000000000)) (hi := (23747673 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 310957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 310957) = 1/(310957 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-23747673 / 50000000) (-474953459 / 1000000000) (Real.log (310957 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (64264613 / 200000000) ≤ -Real.log (1000000 / 1378951) ∧
    -Real.log (1000000 / 1378951) ≤ (160661533 / 500000000) := by
  have h := checkLog_sound (w := (378951 / 2378951)) (n := 12)
    (lo := (64264613 / 200000000)) (hi := (160661533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1378951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1378951 / 1000000) = 1/(1000000 / 1378951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (64264613 / 200000000) (160661533 / 500000000) (Real.log (1378951 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1378951 / 1000000) = -Real.log (1000000 / 1378951) := by
    rw [show ((1378951 / 1000000) : ℝ) = ((1000000 / 1378951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (95269059 / 200000000) ≤ -Real.log (621049 / 1000000) ∧
    -Real.log (621049 / 1000000) ≤ (29771581 / 62500000) := by
  have h := checkLog_sound (w := (378951 / 1621049)) (n := 12)
    (lo := (95269059 / 200000000)) (hi := (29771581 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 621049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 621049) = 1/(621049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-29771581 / 62500000) (-95269059 / 200000000) (Real.log (621049 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (122785483 / 500000000) ≤ -Real.log (1000000 / 1278351) ∧
    -Real.log (1000000 / 1278351) ≤ (245570967 / 1000000000) := by
  have h := checkLog_sound (w := (278351 / 2278351)) (n := 12)
    (lo := (122785483 / 500000000)) (hi := (245570967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1278351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1278351 / 1000000) = 1/(1000000 / 1278351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (122785483 / 500000000) (245570967 / 1000000000) (Real.log (1278351 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1278351 / 1000000) = -Real.log (1000000 / 1278351) := by
    rw [show ((1278351 / 1000000) : ℝ) = ((1000000 / 1278351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (326216407 / 1000000000) ≤ -Real.log (721649 / 1000000) ∧
    -Real.log (721649 / 1000000) ≤ (40777051 / 125000000) := by
  have h := checkLog_sound (w := (278351 / 1721649)) (n := 12)
    (lo := (326216407 / 1000000000)) (hi := (40777051 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 721649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 721649) = 1/(721649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-40777051 / 125000000) (-326216407 / 1000000000) (Real.log (721649 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (123055289 / 500000000) ≤ -Real.log (1000000 / 1279041) ∧
    -Real.log (1000000 / 1279041) ≤ (246110579 / 1000000000) := by
  have h := checkLog_sound (w := (279041 / 2279041)) (n := 12)
    (lo := (123055289 / 500000000)) (hi := (246110579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1279041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1279041 / 1000000) = 1/(1000000 / 1279041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (123055289 / 500000000) (246110579 / 1000000000) (Real.log (1279041 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1279041 / 1000000) = -Real.log (1000000 / 1279041) := by
    rw [show ((1279041 / 1000000) : ℝ) = ((1000000 / 1279041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (20448313 / 62500000) ≤ -Real.log (720959 / 1000000) ∧
    -Real.log (720959 / 1000000) ≤ (327173009 / 1000000000) := by
  have h := checkLog_sound (w := (279041 / 1720959)) (n := 12)
    (lo := (20448313 / 62500000)) (hi := (327173009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 720959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 720959) = 1/(720959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-327173009 / 1000000000) (-20448313 / 62500000) (Real.log (720959 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (397824519 / 500000000) ≤ -Real.log (50000000000 / 110793936139) ∧
    -Real.log (50000000000 / 110793936139) ≤ (9945613 / 12500000) := by
  have h := checkLog_sound (w := (10793936139 / 210793936139)) (n := 12)
    (lo := (51250929 / 500000000)) (hi := (102501859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110793936139 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(110793936139 / 100000000000) = 1/(50000000000 / 110793936139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (397824519 / 500000000) (9945613 / 12500000) (Real.log (110793936139 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (110793936139 / 50000000000) = -Real.log (50000000000 / 110793936139) := by
    rw [show ((110793936139 / 50000000000) : ℝ) = ((50000000000 / 110793936139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (797668359 / 1000000000) ≤ -Real.log (500000000000 / 1110178906979) ∧
    -Real.log (500000000000 / 1110178906979) ≤ (797668361 / 1000000000) := by
  have h := checkLog_sound (w := (110178906979 / 2110178906979)) (n := 12)
    (lo := (104521179 / 1000000000)) (hi := (5226059 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1110178906979 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1110178906979 / 1000000000000) = 1/(500000000000 / 1110178906979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (797668359 / 1000000000) (797668361 / 1000000000) (Real.log (1110178906979 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1110178906979 / 500000000000) = -Real.log (500000000000 / 1110178906979) := by
    rw [show ((1110178906979 / 500000000000) : ℝ) = ((500000000000 / 1110178906979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (285893687 / 500000000) ≤ -Real.log (500000000000 / 885715216123) ∧
    -Real.log (500000000000 / 885715216123) ≤ (4574299 / 8000000) := by
  have h := checkLog_sound (w := (385715216123 / 1385715216123)) (n := 12)
    (lo := (285893687 / 500000000)) (hi := (4574299 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((885715216123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(885715216123 / 500000000000) = 1/(500000000000 / 885715216123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (285893687 / 500000000) (4574299 / 8000000) (Real.log (885715216123 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (885715216123 / 500000000000) = -Real.log (500000000000 / 885715216123) := by
    rw [show ((885715216123 / 500000000000) : ℝ) = ((500000000000 / 885715216123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (573283587 / 1000000000) ≤ -Real.log (500000000000 / 887041426767) ∧
    -Real.log (500000000000 / 887041426767) ≤ (143320897 / 250000000) := by
  have h := checkLog_sound (w := (387041426767 / 1387041426767)) (n := 12)
    (lo := (573283587 / 1000000000)) (hi := (143320897 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887041426767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(887041426767 / 500000000000) = 1/(500000000000 / 887041426767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (573283587 / 1000000000) (143320897 / 250000000) (Real.log (887041426767 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (887041426767 / 500000000000) = -Real.log (500000000000 / 887041426767) := by
    rw [show ((887041426767 / 500000000000) : ℝ) = ((500000000000 / 887041426767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0268
