import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0021
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

theorem reflection_log_1_neg : (39762193 / 100000000) ≤ -Real.log (256 / 381) ∧
    -Real.log (256 / 381) ≤ (397621931 / 1000000000) := by
  have h := checkLog_sound (w := (125 / 637)) (n := 12)
    (lo := (39762193 / 100000000)) (hi := (397621931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381 / 256) = 1/(256 / 381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (39762193 / 100000000) (397621931 / 1000000000) (Real.log (381 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (381 / 256) = -Real.log (256 / 381) := by
    rw [show ((381 / 256) : ℝ) = ((256 / 381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (669980121 / 1000000000) ≤ -Real.log (131 / 256) ∧
    -Real.log (131 / 256) ≤ (334990061 / 500000000) := by
  have h := checkLog_sound (w := (125 / 387)) (n := 12)
    (lo := (669980121 / 1000000000)) (hi := (334990061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 131) = 1/(131 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-334990061 / 500000000) (-669980121 / 1000000000) (Real.log (131 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (198417109 / 500000000) ≤ -Real.log (2560 / 3807) ∧
    -Real.log (2560 / 3807) ≤ (396834219 / 1000000000) := by
  have h := checkLog_sound (w := (1247 / 6367)) (n := 12)
    (lo := (198417109 / 500000000)) (hi := (396834219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3807 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3807 / 2560) = 1/(2560 / 3807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (198417109 / 500000000) (396834219 / 1000000000) (Real.log (3807 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3807 / 2560) = -Real.log (2560 / 3807) := by
    rw [show ((3807 / 2560) : ℝ) = ((2560 / 3807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (667692663 / 1000000000) ≤ -Real.log (1313 / 2560) ∧
    -Real.log (1313 / 2560) ≤ (83461583 / 125000000) := by
  have h := checkLog_sound (w := (1247 / 3873)) (n := 12)
    (lo := (667692663 / 1000000000)) (hi := (83461583 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1313) = 1/(1313 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-83461583 / 125000000) (-667692663 / 1000000000) (Real.log (1313 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (85169903 / 125000000) ≤ -Real.log (128 / 253) ∧
    -Real.log (128 / 253) ≤ (27254369 / 40000000) := by
  have h := checkLog_sound (w := (125 / 381)) (n := 12)
    (lo := (85169903 / 125000000)) (hi := (27254369 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((253 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(253 / 128) = 1/(128 / 253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (85169903 / 125000000) (27254369 / 40000000) (Real.log (253 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (253 / 128) = -Real.log (128 / 253) := by
    rw [show ((253 / 128) : ℝ) = ((128 / 253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (938354493 / 250000000) ≤ -Real.log (3 / 128) ∧
    -Real.log (3 / 128) ≤ (1876708989 / 500000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4 / 3) = 1/(3 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1876708989 / 500000000) (-938354493 / 250000000) (Real.log (3 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2720691 / 4000000) ≤ -Real.log (1280 / 2527) ∧
    -Real.log (1280 / 2527) ≤ (680172751 / 1000000000) := by
  have h := checkLog_sound (w := (1247 / 3807)) (n := 12)
    (lo := (2720691 / 4000000)) (hi := (680172751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2527 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2527 / 1280) = 1/(1280 / 2527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2720691 / 4000000) (680172751 / 1000000000) (Real.log (2527 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2527 / 1280) = -Real.log (1280 / 2527) := by
    rw [show ((2527 / 1280) : ℝ) = ((1280 / 2527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (228631737 / 62500000) ≤ -Real.log (33 / 1280) ∧
    -Real.log (33 / 1280) ≤ (1829053899 / 500000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 33) = 1/(33 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1829053899 / 500000000) (-228631737 / 62500000) (Real.log (33 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (278551173 / 500000000) ≤ -Real.log (1000000 / 1745607) ∧
    -Real.log (1000000 / 1745607) ≤ (557102347 / 1000000000) := by
  have h := checkLog_sound (w := (745607 / 2745607)) (n := 12)
    (lo := (278551173 / 500000000)) (hi := (557102347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1745607 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1745607 / 1000000) = 1/(1000000 / 1745607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (278551173 / 500000000) (557102347 / 1000000000) (Real.log (1745607 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1745607 / 1000000) = -Real.log (1000000 / 1745607) := by
    rw [show ((1745607 / 1000000) : ℝ) = ((1000000 / 1745607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1368874963 / 1000000000) ≤ -Real.log (254393 / 1000000) ∧
    -Real.log (254393 / 1000000) ≤ (273774993 / 200000000) := by
  have h := checkLog_sound (w := (245607 / 754393)) (n := 12)
    (lo := (675727783 / 1000000000)) (hi := (84465973 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 254393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 254393) = 1/(254393 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-273774993 / 200000000) (-1368874963 / 1000000000) (Real.log (254393 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (558625583 / 1000000000) ≤ -Real.log (250000 / 437067) ∧
    -Real.log (250000 / 437067) ≤ (34914099 / 62500000) := by
  have h := checkLog_sound (w := (187067 / 687067)) (n := 12)
    (lo := (558625583 / 1000000000)) (hi := (34914099 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((437067 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(437067 / 250000) = 1/(250000 / 437067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (558625583 / 1000000000) (34914099 / 62500000) (Real.log (437067 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (437067 / 250000) = -Real.log (250000 / 437067) := by
    rw [show ((437067 / 250000) : ℝ) = ((250000 / 437067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (172423781 / 125000000) ≤ -Real.log (62933 / 250000) ∧
    -Real.log (62933 / 250000) ≤ (5517561 / 4000000) := by
  have h := checkLog_sound (w := (62067 / 187933)) (n := 12)
    (lo := (171560767 / 250000000)) (hi := (686243069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 62933) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 62933) = 1/(62933 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-5517561 / 4000000) (-172423781 / 125000000) (Real.log (62933 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (482938363 / 1000000000) ≤ -Real.log (100000 / 162083) ∧
    -Real.log (100000 / 162083) ≤ (120734591 / 250000000) := by
  have h := checkLog_sound (w := (62083 / 262083)) (n := 12)
    (lo := (482938363 / 1000000000)) (hi := (120734591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162083 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162083 / 100000) = 1/(100000 / 162083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (482938363 / 1000000000) (120734591 / 250000000) (Real.log (162083 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (162083 / 100000) = -Real.log (100000 / 162083) := by
    rw [show ((162083 / 100000) : ℝ) = ((100000 / 162083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1551633 / 1600000) ≤ -Real.log (37917 / 100000) ∧
    -Real.log (37917 / 100000) ≤ (969770627 / 1000000000) := by
  have h := checkLog_sound (w := (12083 / 87917)) (n := 12)
    (lo := (55324689 / 200000000)) (hi := (138311723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37917) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 37917) = 1/(37917 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-969770627 / 1000000000) (-1551633 / 1600000) (Real.log (37917 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (121189037 / 250000000) ≤ -Real.log (1000000 / 1623779) ∧
    -Real.log (1000000 / 1623779) ≤ (484756149 / 1000000000) := by
  have h := checkLog_sound (w := (623779 / 2623779)) (n := 12)
    (lo := (121189037 / 250000000)) (hi := (484756149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1623779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1623779 / 1000000) = 1/(1000000 / 1623779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (121189037 / 250000000) (484756149 / 1000000000) (Real.log (1623779 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1623779 / 1000000) = -Real.log (1000000 / 1623779) := by
    rw [show ((1623779 / 1000000) : ℝ) = ((1000000 / 1623779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (977578541 / 1000000000) ≤ -Real.log (376221 / 1000000) ∧
    -Real.log (376221 / 1000000) ≤ (977578543 / 1000000000) := by
  have h := checkLog_sound (w := (123779 / 876221)) (n := 12)
    (lo := (284431361 / 1000000000)) (hi := (142215681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 376221) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 376221) = 1/(376221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-977578543 / 1000000000) (-977578541 / 1000000000) (Real.log (376221 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (481494327 / 250000000) ≤ -Real.log (62500000000 / 428865721541) ∧
    -Real.log (62500000000 / 428865721541) ≤ (1925977311 / 1000000000) := by
  have h := checkLog_sound (w := (178865721541 / 678865721541)) (n := 12)
    (lo := (134920737 / 250000000)) (hi := (539682949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((428865721541 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(428865721541 / 250000000000) = 1/(62500000000 / 428865721541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (481494327 / 250000000) (1925977311 / 1000000000) (Real.log (428865721541 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (428865721541 / 62500000000) = -Real.log (62500000000 / 428865721541) := by
    rw [show ((428865721541 / 62500000000) : ℝ) = ((62500000000 / 428865721541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1938015831 / 1000000000) ≤ -Real.log (50000000000 / 347247866779) ∧
    -Real.log (50000000000 / 347247866779) ≤ (969007917 / 500000000) := by
  have h := checkLog_sound (w := (147247866779 / 547247866779)) (n := 12)
    (lo := (551721471 / 1000000000)) (hi := (1077581 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347247866779 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(347247866779 / 200000000000) = 1/(50000000000 / 347247866779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1938015831 / 1000000000) (969007917 / 500000000) (Real.log (347247866779 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (347247866779 / 50000000000) = -Real.log (50000000000 / 347247866779) := by
    rw [show ((347247866779 / 50000000000) : ℝ) = ((50000000000 / 347247866779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (363177247 / 250000000) ≤ -Real.log (12500000000 / 53433486299) ∧
    -Real.log (12500000000 / 53433486299) ≤ (1452708991 / 1000000000) := by
  have h := checkLog_sound (w := (3433486299 / 103433486299)) (n := 12)
    (lo := (16603657 / 250000000)) (hi := (66414629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53433486299 / 50000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(53433486299 / 50000000000) = 1/(12500000000 / 53433486299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (363177247 / 250000000) (1452708991 / 1000000000) (Real.log (53433486299 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (53433486299 / 12500000000) = -Real.log (12500000000 / 53433486299) := by
    rw [show ((53433486299 / 12500000000) : ℝ) = ((12500000000 / 53433486299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1462334689 / 1000000000) ≤ -Real.log (125000000000 / 539503044753) ∧
    -Real.log (125000000000 / 539503044753) ≤ (365583673 / 250000000) := by
  have h := checkLog_sound (w := (39503044753 / 1039503044753)) (n := 12)
    (lo := (76040329 / 1000000000)) (hi := (7604033 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539503044753 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(539503044753 / 500000000000) = 1/(125000000000 / 539503044753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1462334689 / 1000000000) (365583673 / 250000000) (Real.log (539503044753 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (539503044753 / 125000000000) = -Real.log (125000000000 / 539503044753) := by
    rw [show ((539503044753 / 125000000000) : ℝ) = ((125000000000 / 539503044753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0021
