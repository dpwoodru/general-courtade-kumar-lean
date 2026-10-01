import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell074
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (64423983 / 250000000) ≤ -Real.log (1024 / 1325) ∧
    -Real.log (1024 / 1325) ≤ (257695933 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 2349)) (n := 12)
    (lo := (64423983 / 250000000)) (hi := (257695933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1325 / 1024) = 1/(1024 / 1325) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (64423983 / 250000000) (257695933 / 1000000000) (Real.log (1325 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1325 / 1024) = -Real.log (1024 / 1325) := by
    rw [show ((1325 / 1024) : ℝ) = ((1024 / 1325) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (348062583 / 1000000000) ≤ -Real.log (723 / 1024) ∧
    -Real.log (723 / 1024) ≤ (43507823 / 125000000) := by
  have h := checkLog_sound (w := (301 / 1747)) (n := 12)
    (lo := (348062583 / 1000000000)) (hi := (43507823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 723) = 1/(723 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-43507823 / 125000000) (-348062583 / 1000000000) (Real.log (723 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (257243 / 1000000) ≤ -Real.log (2560 / 3311) ∧
    -Real.log (2560 / 3311) ≤ (257243001 / 1000000000) := by
  have h := checkLog_sound (w := (751 / 5871)) (n := 12)
    (lo := (257243 / 1000000)) (hi := (257243001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3311 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3311 / 2560) = 1/(2560 / 3311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (257243 / 1000000) (257243001 / 1000000000) (Real.log (3311 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3311 / 2560) = -Real.log (2560 / 3311) := by
    rw [show ((3311 / 2560) : ℝ) = ((2560 / 3311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (86808263 / 250000000) ≤ -Real.log (1809 / 2560) ∧
    -Real.log (1809 / 2560) ≤ (347233053 / 1000000000) := by
  have h := checkLog_sound (w := (751 / 4369)) (n := 12)
    (lo := (86808263 / 250000000)) (hi := (347233053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1809) = 1/(1809 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-347233053 / 1000000000) (-86808263 / 250000000) (Real.log (1809 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (94568721 / 500000000) ≤ -Real.log (1000000 / 1208207) ∧
    -Real.log (1000000 / 1208207) ≤ (189137443 / 1000000000) := by
  have h := checkLog_sound (w := (208207 / 2208207)) (n := 12)
    (lo := (94568721 / 500000000)) (hi := (189137443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1208207 / 1000000) = 1/(1000000 / 1208207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (94568721 / 500000000) (189137443 / 1000000000) (Real.log (1208207 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1208207 / 1000000) = -Real.log (1000000 / 1208207) := by
    rw [show ((1208207 / 1000000) : ℝ) = ((1000000 / 1208207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (58363821 / 250000000) ≤ -Real.log (791793 / 1000000) ∧
    -Real.log (791793 / 1000000) ≤ (46691057 / 200000000) := by
  have h := checkLog_sound (w := (208207 / 1791793)) (n := 12)
    (lo := (58363821 / 250000000)) (hi := (46691057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 791793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 791793) = 1/(791793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-46691057 / 200000000) (-58363821 / 250000000) (Real.log (791793 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (189485831 / 1000000000) ≤ -Real.log (250000 / 302157) ∧
    -Real.log (250000 / 302157) ≤ (23685729 / 125000000) := by
  have h := checkLog_sound (w := (52157 / 552157)) (n := 12)
    (lo := (189485831 / 1000000000)) (hi := (23685729 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302157 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302157 / 250000) = 1/(250000 / 302157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (189485831 / 1000000000) (23685729 / 125000000) (Real.log (302157 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (302157 / 250000) = -Real.log (250000 / 302157) := by
    rw [show ((302157 / 250000) : ℝ) = ((250000 / 302157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (23398713 / 100000000) ≤ -Real.log (197843 / 250000) ∧
    -Real.log (197843 / 250000) ≤ (233987131 / 1000000000) := by
  have h := checkLog_sound (w := (52157 / 447843)) (n := 12)
    (lo := (23398713 / 100000000)) (hi := (233987131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 197843) = 1/(197843 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-233987131 / 1000000000) (-23398713 / 100000000) (Real.log (197843 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (138905053 / 1000000000) ≤ -Real.log (200000 / 229803) ∧
    -Real.log (200000 / 229803) ≤ (69452527 / 500000000) := by
  have h := checkLog_sound (w := (29803 / 429803)) (n := 12)
    (lo := (138905053 / 1000000000)) (hi := (69452527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229803 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229803 / 200000) = 1/(200000 / 229803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (138905053 / 1000000000) (69452527 / 500000000) (Real.log (229803 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (229803 / 200000) = -Real.log (200000 / 229803) := by
    rw [show ((229803 / 200000) : ℝ) = ((200000 / 229803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (20170097 / 125000000) ≤ -Real.log (170197 / 200000) ∧
    -Real.log (170197 / 200000) ≤ (161360777 / 1000000000) := by
  have h := checkLog_sound (w := (29803 / 370197)) (n := 12)
    (lo := (20170097 / 125000000)) (hi := (161360777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 170197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 170197) = 1/(170197 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-161360777 / 1000000000) (-20170097 / 125000000) (Real.log (170197 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (139173073 / 1000000000) ≤ -Real.log (1000000 / 1149323) ∧
    -Real.log (1000000 / 1149323) ≤ (69586537 / 500000000) := by
  have h := checkLog_sound (w := (149323 / 2149323)) (n := 12)
    (lo := (139173073 / 1000000000)) (hi := (69586537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1149323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1149323 / 1000000) = 1/(1000000 / 1149323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (139173073 / 1000000000) (69586537 / 500000000) (Real.log (1149323 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1149323 / 1000000) = -Real.log (1000000 / 1149323) := by
    rw [show ((1149323 / 1000000) : ℝ) = ((1000000 / 1149323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (6468911 / 40000000) ≤ -Real.log (850677 / 1000000) ∧
    -Real.log (850677 / 1000000) ≤ (20215347 / 125000000) := by
  have h := checkLog_sound (w := (149323 / 1850677)) (n := 12)
    (lo := (6468911 / 40000000)) (hi := (20215347 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 850677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 850677) = 1/(850677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-20215347 / 125000000) (-6468911 / 40000000) (Real.log (850677 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (151119013 / 250000000) ≤ -Real.log (500000000000 / 915146489773) ∧
    -Real.log (500000000000 / 915146489773) ≤ (604476053 / 1000000000) := by
  have h := checkLog_sound (w := (415146489773 / 1415146489773)) (n := 12)
    (lo := (151119013 / 250000000)) (hi := (604476053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((915146489773 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(915146489773 / 500000000000) = 1/(500000000000 / 915146489773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (151119013 / 250000000) (604476053 / 1000000000) (Real.log (915146489773 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (915146489773 / 500000000000) = -Real.log (500000000000 / 915146489773) := by
    rw [show ((915146489773 / 500000000000) : ℝ) = ((500000000000 / 915146489773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (151439629 / 250000000) ≤ -Real.log (500000000000 / 916320885201) ∧
    -Real.log (500000000000 / 916320885201) ≤ (605758517 / 1000000000) := by
  have h := checkLog_sound (w := (416320885201 / 1416320885201)) (n := 12)
    (lo := (151439629 / 250000000)) (hi := (605758517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((916320885201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(916320885201 / 500000000000) = 1/(500000000000 / 916320885201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (151439629 / 250000000) (605758517 / 1000000000) (Real.log (916320885201 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (916320885201 / 500000000000) = -Real.log (500000000000 / 916320885201) := by
    rw [show ((916320885201 / 500000000000) : ℝ) = ((500000000000 / 916320885201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (422592727 / 1000000000) ≤ -Real.log (500000000000 / 762956353491) ∧
    -Real.log (500000000000 / 762956353491) ≤ (52824091 / 125000000) := by
  have h := checkLog_sound (w := (262956353491 / 1262956353491)) (n := 12)
    (lo := (422592727 / 1000000000)) (hi := (52824091 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((762956353491 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(762956353491 / 500000000000) = 1/(500000000000 / 762956353491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (422592727 / 1000000000) (52824091 / 125000000) (Real.log (762956353491 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (762956353491 / 500000000000) = -Real.log (500000000000 / 762956353491) := by
    rw [show ((762956353491 / 500000000000) : ℝ) = ((500000000000 / 762956353491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (211736481 / 500000000) ≤ -Real.log (250000000000 / 381814115233) ∧
    -Real.log (250000000000 / 381814115233) ≤ (423472963 / 1000000000) := by
  have h := checkLog_sound (w := (131814115233 / 631814115233)) (n := 12)
    (lo := (211736481 / 500000000)) (hi := (423472963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381814115233 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381814115233 / 250000000000) = 1/(250000000000 / 381814115233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (211736481 / 500000000) (423472963 / 1000000000) (Real.log (381814115233 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (381814115233 / 250000000000) = -Real.log (250000000000 / 381814115233) := by
    rw [show ((381814115233 / 250000000000) : ℝ) = ((250000000000 / 381814115233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (30026583 / 100000000) ≤ -Real.log (62500000000 / 84388605557) ∧
    -Real.log (62500000000 / 84388605557) ≤ (300265831 / 1000000000) := by
  have h := checkLog_sound (w := (21888605557 / 146888605557)) (n := 12)
    (lo := (30026583 / 100000000)) (hi := (300265831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84388605557 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84388605557 / 62500000000) = 1/(62500000000 / 84388605557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (30026583 / 100000000) (300265831 / 1000000000) (Real.log (84388605557 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (84388605557 / 62500000000) = -Real.log (62500000000 / 84388605557) := by
    rw [show ((84388605557 / 62500000000) : ℝ) = ((62500000000 / 84388605557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (300895849 / 1000000000) ≤ -Real.log (500000000000 / 675534309733) ∧
    -Real.log (500000000000 / 675534309733) ≤ (6017917 / 20000000) := by
  have h := checkLog_sound (w := (175534309733 / 1175534309733)) (n := 12)
    (lo := (300895849 / 1000000000)) (hi := (6017917 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675534309733 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675534309733 / 500000000000) = 1/(500000000000 / 675534309733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (300895849 / 1000000000) (6017917 / 20000000) (Real.log (675534309733 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (675534309733 / 500000000000) = -Real.log (500000000000 / 675534309733) := by
    rw [show ((675534309733 / 500000000000) : ℝ) = ((500000000000 / 675534309733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (11274851 / 500000000) ≤ -Real.log (977702641671 / 1000000000000) ∧
    -Real.log (977702641671 / 1000000000000) ≤ (22549703 / 1000000000) := by
  have h := checkLog_sound (w := (22297358329 / 1977702641671)) (n := 12)
    (lo := (11274851 / 500000000)) (hi := (22549703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977702641671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977702641671) = 1/(977702641671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-22549703 / 1000000000) (-11274851 / 500000000) (Real.log (977702641671 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (22455723 / 1000000000) ≤ -Real.log (39111781191 / 40000000000) ∧
    -Real.log (39111781191 / 40000000000) ≤ (5613931 / 250000000) := by
  have h := checkLog_sound (w := (888218809 / 79111781191)) (n := 12)
    (lo := (22455723 / 1000000000)) (hi := (5613931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39111781191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39111781191) = 1/(39111781191 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5613931 / 250000000) (-22455723 / 1000000000) (Real.log (39111781191 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell074
