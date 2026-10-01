import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell070
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

theorem reflection_log_1_neg : (255882969 / 1000000000) ≤ -Real.log (5120 / 6613) ∧
    -Real.log (5120 / 6613) ≤ (25588297 / 100000000) := by
  have h := checkLog_sound (w := (1493 / 11733)) (n := 12)
    (lo := (255882969 / 1000000000)) (hi := (25588297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6613 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6613 / 5120) = 1/(5120 / 6613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (255882969 / 1000000000) (25588297 / 100000000) (Real.log (6613 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6613 / 5120) = -Real.log (5120 / 6613) := by
    rw [show ((6613 / 5120) : ℝ) = ((5120 / 6613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (172374289 / 500000000) ≤ -Real.log (3627 / 5120) ∧
    -Real.log (3627 / 5120) ≤ (344748579 / 1000000000) := by
  have h := checkLog_sound (w := (1493 / 8747)) (n := 12)
    (lo := (172374289 / 500000000)) (hi := (344748579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3627) = 1/(3627 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-344748579 / 1000000000) (-172374289 / 500000000) (Real.log (3627 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (127714607 / 500000000) ≤ -Real.log (512 / 661) ∧
    -Real.log (512 / 661) ≤ (51085843 / 200000000) := by
  have h := checkLog_sound (w := (149 / 1173)) (n := 12)
    (lo := (127714607 / 500000000)) (hi := (51085843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661 / 512) = 1/(512 / 661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (127714607 / 500000000) (51085843 / 200000000) (Real.log (661 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (661 / 512) = -Real.log (512 / 661) := by
    rw [show ((661 / 512) : ℝ) = ((512 / 661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (34392179 / 100000000) ≤ -Real.log (363 / 512) ∧
    -Real.log (363 / 512) ≤ (343921791 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 875)) (n := 12)
    (lo := (34392179 / 100000000)) (hi := (343921791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 363) = 1/(363 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-343921791 / 1000000000) (-34392179 / 100000000) (Real.log (363 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (187749299 / 1000000000) ≤ -Real.log (1000000 / 1206531) ∧
    -Real.log (1000000 / 1206531) ≤ (1877493 / 10000000) := by
  have h := checkLog_sound (w := (206531 / 2206531)) (n := 12)
    (lo := (187749299 / 1000000000)) (hi := (1877493 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206531 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206531 / 1000000) = 1/(1000000 / 1206531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (187749299 / 1000000000) (1877493 / 10000000) (Real.log (1206531 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1206531 / 1000000) = -Real.log (1000000 / 1206531) := by
    rw [show ((1206531 / 1000000) : ℝ) = ((1000000 / 1206531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (231340807 / 1000000000) ≤ -Real.log (793469 / 1000000) ∧
    -Real.log (793469 / 1000000) ≤ (28917601 / 125000000) := by
  have h := checkLog_sound (w := (206531 / 1793469)) (n := 12)
    (lo := (231340807 / 1000000000)) (hi := (28917601 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793469) = 1/(793469 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-28917601 / 125000000) (-231340807 / 1000000000) (Real.log (793469 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2939021 / 15625000) ≤ -Real.log (1000000 / 1206951) ∧
    -Real.log (1000000 / 1206951) ≤ (37619469 / 200000000) := by
  have h := checkLog_sound (w := (206951 / 2206951)) (n := 12)
    (lo := (2939021 / 15625000)) (hi := (37619469 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1206951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1206951 / 1000000) = 1/(1000000 / 1206951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2939021 / 15625000) (37619469 / 200000000) (Real.log (1206951 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1206951 / 1000000) = -Real.log (1000000 / 1206951) := by
    rw [show ((1206951 / 1000000) : ℝ) = ((1000000 / 1206951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (57967567 / 250000000) ≤ -Real.log (793049 / 1000000) ∧
    -Real.log (793049 / 1000000) ≤ (231870269 / 1000000000) := by
  have h := checkLog_sound (w := (206951 / 1793049)) (n := 12)
    (lo := (57967567 / 250000000)) (hi := (231870269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 793049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 793049) = 1/(793049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-231870269 / 1000000000) (-57967567 / 250000000) (Real.log (793049 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (6891787 / 50000000) ≤ -Real.log (1000000 / 1147787) ∧
    -Real.log (1000000 / 1147787) ≤ (137835741 / 1000000000) := by
  have h := checkLog_sound (w := (147787 / 2147787)) (n := 12)
    (lo := (6891787 / 50000000)) (hi := (137835741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147787 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1147787 / 1000000) = 1/(1000000 / 1147787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (6891787 / 50000000) (137835741 / 1000000000) (Real.log (1147787 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1147787 / 1000000) = -Real.log (1000000 / 1147787) := by
    rw [show ((1147787 / 1000000) : ℝ) = ((1000000 / 1147787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (159918783 / 1000000000) ≤ -Real.log (852213 / 1000000) ∧
    -Real.log (852213 / 1000000) ≤ (2498731 / 15625000) := by
  have h := checkLog_sound (w := (147787 / 1852213)) (n := 12)
    (lo := (159918783 / 1000000000)) (hi := (2498731 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 852213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 852213) = 1/(852213 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2498731 / 15625000) (-159918783 / 1000000000) (Real.log (852213 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (138104047 / 1000000000) ≤ -Real.log (200000 / 229619) ∧
    -Real.log (200000 / 229619) ≤ (8631503 / 62500000) := by
  have h := checkLog_sound (w := (29619 / 429619)) (n := 12)
    (lo := (138104047 / 1000000000)) (hi := (8631503 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229619 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229619 / 200000) = 1/(200000 / 229619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (138104047 / 1000000000) (8631503 / 62500000) (Real.log (229619 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (229619 / 200000) = -Real.log (200000 / 229619) := by
    rw [show ((229619 / 200000) : ℝ) = ((200000 / 229619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (8014013 / 50000000) ≤ -Real.log (170381 / 200000) ∧
    -Real.log (170381 / 200000) ≤ (160280261 / 1000000000) := by
  have h := checkLog_sound (w := (29619 / 370381)) (n := 12)
    (lo := (8014013 / 50000000)) (hi := (160280261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 170381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 170381) = 1/(170381 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-160280261 / 1000000000) (-8014013 / 50000000) (Real.log (170381 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (119870201 / 200000000) ≤ -Real.log (500000000000 / 910468319559) ∧
    -Real.log (500000000000 / 910468319559) ≤ (299675503 / 500000000) := by
  have h := checkLog_sound (w := (410468319559 / 1410468319559)) (n := 12)
    (lo := (119870201 / 200000000)) (hi := (299675503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((910468319559 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(910468319559 / 500000000000) = 1/(500000000000 / 910468319559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (119870201 / 200000000) (299675503 / 500000000) (Real.log (910468319559 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (910468319559 / 500000000000) = -Real.log (500000000000 / 910468319559) := by
    rw [show ((910468319559 / 500000000000) : ℝ) = ((500000000000 / 910468319559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (150157887 / 250000000) ≤ -Real.log (500000000000 / 911634960023) ∧
    -Real.log (500000000000 / 911634960023) ≤ (600631549 / 1000000000) := by
  have h := checkLog_sound (w := (411634960023 / 1411634960023)) (n := 12)
    (lo := (150157887 / 250000000)) (hi := (600631549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911634960023 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911634960023 / 500000000000) = 1/(500000000000 / 911634960023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (150157887 / 250000000) (600631549 / 1000000000) (Real.log (911634960023 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (911634960023 / 500000000000) = -Real.log (500000000000 / 911634960023) := by
    rw [show ((911634960023 / 500000000000) : ℝ) = ((500000000000 / 911634960023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (419090107 / 1000000000) ≤ -Real.log (20000000000 / 30411547269) ∧
    -Real.log (20000000000 / 30411547269) ≤ (104772527 / 250000000) := by
  have h := checkLog_sound (w := (10411547269 / 50411547269)) (n := 12)
    (lo := (419090107 / 1000000000)) (hi := (104772527 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30411547269 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30411547269 / 20000000000) = 1/(20000000000 / 30411547269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (419090107 / 1000000000) (104772527 / 250000000) (Real.log (30411547269 / 20000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (30411547269 / 20000000000) = -Real.log (20000000000 / 30411547269) := by
    rw [show ((30411547269 / 20000000000) : ℝ) = ((20000000000 / 30411547269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (419967613 / 1000000000) ≤ -Real.log (250000000000 / 380478066299) ∧
    -Real.log (250000000000 / 380478066299) ≤ (209983807 / 500000000) := by
  have h := checkLog_sound (w := (130478066299 / 630478066299)) (n := 12)
    (lo := (419967613 / 1000000000)) (hi := (209983807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((380478066299 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(380478066299 / 250000000000) = 1/(250000000000 / 380478066299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (419967613 / 1000000000) (209983807 / 500000000) (Real.log (380478066299 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (380478066299 / 250000000000) = -Real.log (250000000000 / 380478066299) := by
    rw [show ((380478066299 / 250000000000) : ℝ) = ((250000000000 / 380478066299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (74438631 / 250000000) ≤ -Real.log (62500000000 / 84176945787) ∧
    -Real.log (62500000000 / 84176945787) ≤ (11910181 / 40000000) := by
  have h := checkLog_sound (w := (21676945787 / 146676945787)) (n := 12)
    (lo := (74438631 / 250000000)) (hi := (11910181 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((84176945787 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(84176945787 / 62500000000) = 1/(62500000000 / 84176945787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (74438631 / 250000000) (11910181 / 40000000) (Real.log (84176945787 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (84176945787 / 62500000000) = -Real.log (62500000000 / 84176945787) := by
    rw [show ((84176945787 / 62500000000) : ℝ) = ((62500000000 / 84176945787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (298384307 / 1000000000) ≤ -Real.log (250000000000 / 336919903041) ∧
    -Real.log (250000000000 / 336919903041) ≤ (74596077 / 250000000) := by
  have h := checkLog_sound (w := (86919903041 / 586919903041)) (n := 12)
    (lo := (298384307 / 1000000000)) (hi := (74596077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336919903041 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336919903041 / 250000000000) = 1/(250000000000 / 336919903041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (298384307 / 1000000000) (74596077 / 250000000) (Real.log (336919903041 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (336919903041 / 250000000000) = -Real.log (250000000000 / 336919903041) := by
    rw [show ((336919903041 / 250000000000) : ℝ) = ((250000000000 / 336919903041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (22176213 / 1000000000) ≤ -Real.log (39122714839 / 40000000000) ∧
    -Real.log (39122714839 / 40000000000) ≤ (11088107 / 500000000) := by
  have h := checkLog_sound (w := (877285161 / 79122714839)) (n := 12)
    (lo := (22176213 / 1000000000)) (hi := (11088107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39122714839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39122714839) = 1/(39122714839 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-11088107 / 500000000) (-22176213 / 1000000000) (Real.log (39122714839 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (11041521 / 500000000) ≤ -Real.log (978159002631 / 1000000000000) ∧
    -Real.log (978159002631 / 1000000000000) ≤ (22083043 / 1000000000) := by
  have h := checkLog_sound (w := (21840997369 / 1978159002631)) (n := 12)
    (lo := (11041521 / 500000000)) (hi := (22083043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978159002631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978159002631) = 1/(978159002631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-22083043 / 1000000000) (-11041521 / 500000000) (Real.log (978159002631 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell070
