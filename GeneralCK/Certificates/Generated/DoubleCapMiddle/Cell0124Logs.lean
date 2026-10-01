import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0124
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

theorem reflection_log_1_neg : (313041383 / 1000000000) ≤ -Real.log (2560 / 3501) ∧
    -Real.log (2560 / 3501) ≤ (39130173 / 125000000) := by
  have h := checkLog_sound (w := (941 / 6061)) (n := 12)
    (lo := (313041383 / 1000000000)) (hi := (39130173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3501 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3501 / 2560) = 1/(2560 / 3501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (313041383 / 1000000000) (39130173 / 125000000) (Real.log (3501 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3501 / 2560) = -Real.log (2560 / 3501) := by
    rw [show ((3501 / 2560) : ℝ) = ((2560 / 3501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (458198583 / 1000000000) ≤ -Real.log (1619 / 2560) ∧
    -Real.log (1619 / 2560) ≤ (57274823 / 125000000) := by
  have h := checkLog_sound (w := (941 / 4179)) (n := 12)
    (lo := (458198583 / 1000000000)) (hi := (57274823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1619) = 1/(1619 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-57274823 / 125000000) (-458198583 / 1000000000) (Real.log (1619 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (156092059 / 500000000) ≤ -Real.log (1280 / 1749) ∧
    -Real.log (1280 / 1749) ≤ (312184119 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 3029)) (n := 12)
    (lo := (156092059 / 500000000)) (hi := (312184119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1749 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1749 / 1280) = 1/(1280 / 1749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (156092059 / 500000000) (312184119 / 1000000000) (Real.log (1749 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1749 / 1280) = -Real.log (1280 / 1749) := by
    rw [show ((1749 / 1280) : ℝ) = ((1280 / 1749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (228173651 / 500000000) ≤ -Real.log (811 / 1280) ∧
    -Real.log (811 / 1280) ≤ (456347303 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 2091)) (n := 12)
    (lo := (228173651 / 500000000)) (hi := (456347303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 811) = 1/(811 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-456347303 / 1000000000) (-228173651 / 500000000) (Real.log (811 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (275548733 / 500000000) ≤ -Real.log (1280 / 2221) ∧
    -Real.log (1280 / 2221) ≤ (551097467 / 1000000000) := by
  have h := checkLog_sound (w := (941 / 3501)) (n := 12)
    (lo := (275548733 / 500000000)) (hi := (551097467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2221 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2221 / 1280) = 1/(1280 / 2221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (275548733 / 500000000) (551097467 / 1000000000) (Real.log (2221 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2221 / 1280) = -Real.log (1280 / 2221) := by
    rw [show ((2221 / 1280) : ℝ) = ((1280 / 2221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (83038453 / 62500000) ≤ -Real.log (339 / 1280) ∧
    -Real.log (339 / 1280) ≤ (5314461 / 4000000) := by
  have h := checkLog_sound (w := (301 / 979)) (n := 12)
    (lo := (158867017 / 250000000)) (hi := (635468069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 339) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 339) = 1/(339 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5314461 / 4000000) (-83038453 / 62500000) (Real.log (339 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (54974581 / 100000000) ≤ -Real.log (640 / 1109) ∧
    -Real.log (640 / 1109) ≤ (549745811 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 1749)) (n := 12)
    (lo := (54974581 / 100000000)) (hi := (549745811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1109 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1109 / 640) = 1/(640 / 1109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (54974581 / 100000000) (549745811 / 1000000000) (Real.log (1109 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1109 / 640) = -Real.log (640 / 1109) := by
    rw [show ((1109 / 640) : ℝ) = ((640 / 1109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1319804619 / 1000000000) ≤ -Real.log (171 / 640) ∧
    -Real.log (171 / 640) ≤ (1319804621 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 491)) (n := 12)
    (lo := (626657439 / 1000000000)) (hi := (3916609 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 171) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 171) = 1/(171 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1319804621 / 1000000000) (-1319804619 / 1000000000) (Real.log (171 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (427573571 / 1000000000) ≤ -Real.log (250000 / 383383) ∧
    -Real.log (250000 / 383383) ≤ (106893393 / 250000000) := by
  have h := checkLog_sound (w := (133383 / 633383)) (n := 12)
    (lo := (427573571 / 1000000000)) (hi := (106893393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383383 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383383 / 250000) = 1/(250000 / 383383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (427573571 / 1000000000) (106893393 / 250000000) (Real.log (383383 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (383383 / 250000) = -Real.log (250000 / 383383) := by
    rw [show ((383383 / 250000) : ℝ) = ((250000 / 383383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (23830183 / 31250000) ≤ -Real.log (116617 / 250000) ∧
    -Real.log (116617 / 250000) ≤ (381282929 / 500000000) := by
  have h := checkLog_sound (w := (8383 / 241617)) (n := 12)
    (lo := (17354669 / 250000000)) (hi := (69418677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 116617) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 116617) = 1/(116617 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-381282929 / 500000000) (-23830183 / 31250000) (Real.log (116617 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (8575493 / 20000000) ≤ -Real.log (8000 / 12283) ∧
    -Real.log (8000 / 12283) ≤ (428774651 / 1000000000) := by
  have h := checkLog_sound (w := (4283 / 20283)) (n := 12)
    (lo := (8575493 / 20000000)) (hi := (428774651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12283 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12283 / 8000) = 1/(8000 / 12283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (8575493 / 20000000) (428774651 / 1000000000) (Real.log (12283 / 8000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (12283 / 8000) = -Real.log (8000 / 12283) := by
    rw [show ((12283 / 8000) : ℝ) = ((8000 / 12283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (766524649 / 1000000000) ≤ -Real.log (3717 / 8000) ∧
    -Real.log (3717 / 8000) ≤ (766524651 / 1000000000) := by
  have h := checkLog_sound (w := (283 / 7717)) (n := 12)
    (lo := (73377469 / 1000000000)) (hi := (7337747 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3717) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4000 / 3717) = 1/(3717 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-766524651 / 1000000000) (-766524649 / 1000000000) (Real.log (3717 / 8000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (171571043 / 500000000) ≤ -Real.log (1000000 / 1409369) ∧
    -Real.log (1000000 / 1409369) ≤ (343142087 / 1000000000) := by
  have h := checkLog_sound (w := (409369 / 2409369)) (n := 12)
    (lo := (171571043 / 500000000)) (hi := (343142087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1409369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1409369 / 1000000) = 1/(1000000 / 1409369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (171571043 / 500000000) (343142087 / 1000000000) (Real.log (1409369 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1409369 / 1000000) = -Real.log (1000000 / 1409369) := by
    rw [show ((1409369 / 1000000) : ℝ) = ((1000000 / 1409369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (263281911 / 500000000) ≤ -Real.log (590631 / 1000000) ∧
    -Real.log (590631 / 1000000) ≤ (526563823 / 1000000000) := by
  have h := checkLog_sound (w := (409369 / 1590631)) (n := 12)
    (lo := (263281911 / 500000000)) (hi := (526563823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 590631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 590631) = 1/(590631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-526563823 / 1000000000) (-263281911 / 500000000) (Real.log (590631 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (344314973 / 1000000000) ≤ -Real.log (1000000 / 1411023) ∧
    -Real.log (1000000 / 1411023) ≤ (172157487 / 500000000) := by
  have h := checkLog_sound (w := (411023 / 2411023)) (n := 12)
    (lo := (344314973 / 1000000000)) (hi := (172157487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1411023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1411023 / 1000000) = 1/(1000000 / 1411023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (344314973 / 1000000000) (172157487 / 500000000) (Real.log (1411023 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1411023 / 1000000) = -Real.log (1000000 / 1411023) := by
    rw [show ((1411023 / 1000000) : ℝ) = ((1000000 / 1411023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (105873629 / 200000000) ≤ -Real.log (588977 / 1000000) ∧
    -Real.log (588977 / 1000000) ≤ (264684073 / 500000000) := by
  have h := checkLog_sound (w := (411023 / 1588977)) (n := 12)
    (lo := (105873629 / 200000000)) (hi := (264684073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 588977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 588977) = 1/(588977 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-264684073 / 500000000) (-105873629 / 200000000) (Real.log (588977 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (297534857 / 250000000) ≤ -Real.log (125000000000 / 410942444069) ∧
    -Real.log (125000000000 / 410942444069) ≤ (119013943 / 100000000) := by
  have h := checkLog_sound (w := (160942444069 / 660942444069)) (n := 12)
    (lo := (62124031 / 125000000)) (hi := (496992249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410942444069 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(410942444069 / 250000000000) = 1/(125000000000 / 410942444069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (297534857 / 250000000) (119013943 / 100000000) (Real.log (410942444069 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (410942444069 / 125000000000) = -Real.log (125000000000 / 410942444069) := by
    rw [show ((410942444069 / 125000000000) : ℝ) = ((125000000000 / 410942444069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (11952993 / 10000000) ≤ -Real.log (100000000000 / 330454667743) ∧
    -Real.log (100000000000 / 330454667743) ≤ (597649651 / 500000000) := by
  have h := checkLog_sound (w := (130454667743 / 530454667743)) (n := 12)
    (lo := (12553803 / 25000000)) (hi := (502152121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330454667743 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(330454667743 / 200000000000) = 1/(100000000000 / 330454667743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (11952993 / 10000000) (597649651 / 500000000) (Real.log (330454667743 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (330454667743 / 100000000000) = -Real.log (100000000000 / 330454667743) := by
    rw [show ((330454667743 / 100000000000) : ℝ) = ((100000000000 / 330454667743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (869705907 / 1000000000) ≤ -Real.log (50000000000 / 119310449333) ∧
    -Real.log (50000000000 / 119310449333) ≤ (869705909 / 1000000000) := by
  have h := checkLog_sound (w := (19310449333 / 219310449333)) (n := 12)
    (lo := (176558727 / 1000000000)) (hi := (22069841 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119310449333 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(119310449333 / 100000000000) = 1/(50000000000 / 119310449333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (869705907 / 1000000000) (869705909 / 1000000000) (Real.log (119310449333 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (119310449333 / 50000000000) = -Real.log (50000000000 / 119310449333) := by
    rw [show ((119310449333 / 50000000000) : ℝ) = ((50000000000 / 119310449333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (436841559 / 500000000) ≤ -Real.log (250000000000 / 598929584687) ∧
    -Real.log (250000000000 / 598929584687) ≤ (10921039 / 12500000) := by
  have h := checkLog_sound (w := (98929584687 / 1098929584687)) (n := 12)
    (lo := (90267969 / 500000000)) (hi := (180535939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598929584687 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(598929584687 / 500000000000) = 1/(250000000000 / 598929584687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (436841559 / 500000000) (10921039 / 12500000) (Real.log (598929584687 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (598929584687 / 250000000000) = -Real.log (250000000000 / 598929584687) := by
    rw [show ((598929584687 / 250000000000) : ℝ) = ((250000000000 / 598929584687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0124
