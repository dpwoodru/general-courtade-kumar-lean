import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0374
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

theorem reflection_log_1_neg : (206442359 / 1000000000) ≤ -Real.log (2560 / 3147) ∧
    -Real.log (2560 / 3147) ≤ (5161059 / 25000000) := by
  have h := checkLog_sound (w := (587 / 5707)) (n := 12)
    (lo := (206442359 / 1000000000)) (hi := (5161059 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3147 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3147 / 2560) = 1/(2560 / 3147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (206442359 / 1000000000) (5161059 / 25000000) (Real.log (3147 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3147 / 2560) = -Real.log (2560 / 3147) := by
    rw [show ((3147 / 2560) : ℝ) = ((2560 / 3147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (260452031 / 1000000000) ≤ -Real.log (1973 / 2560) ∧
    -Real.log (1973 / 2560) ≤ (4069563 / 15625000) := by
  have h := checkLog_sound (w := (587 / 4533)) (n := 12)
    (lo := (260452031 / 1000000000)) (hi := (4069563 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1973) = 1/(1973 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-4069563 / 15625000) (-260452031 / 1000000000) (Real.log (1973 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (25775501 / 125000000) ≤ -Real.log (2048 / 2517) ∧
    -Real.log (2048 / 2517) ≤ (206204009 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 4565)) (n := 12)
    (lo := (25775501 / 125000000)) (hi := (206204009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2517 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2517 / 2048) = 1/(2048 / 2517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (25775501 / 125000000) (206204009 / 1000000000) (Real.log (2517 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2517 / 2048) = -Real.log (2048 / 2517) := by
    rw [show ((2517 / 2048) : ℝ) = ((2048 / 2517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (260071971 / 1000000000) ≤ -Real.log (1579 / 2048) ∧
    -Real.log (1579 / 2048) ≤ (65017993 / 250000000) := by
  have h := checkLog_sound (w := (469 / 3627)) (n := 12)
    (lo := (260071971 / 1000000000)) (hi := (65017993 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1579) = 1/(1579 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65017993 / 250000000) (-260071971 / 1000000000) (Real.log (1579 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (188736393 / 500000000) ≤ -Real.log (1280 / 1867) ∧
    -Real.log (1280 / 1867) ≤ (377472787 / 1000000000) := by
  have h := checkLog_sound (w := (587 / 3147)) (n := 12)
    (lo := (188736393 / 500000000)) (hi := (377472787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1867 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1867 / 1280) = 1/(1280 / 1867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (188736393 / 500000000) (377472787 / 1000000000) (Real.log (1867 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1867 / 1280) = -Real.log (1280 / 1867) := by
    rw [show ((1867 / 1280) : ℝ) = ((1280 / 1867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (613585357 / 1000000000) ≤ -Real.log (693 / 1280) ∧
    -Real.log (693 / 1280) ≤ (306792679 / 500000000) := by
  have h := checkLog_sound (w := (587 / 1973)) (n := 12)
    (lo := (613585357 / 1000000000)) (hi := (306792679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 693) = 1/(693 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-306792679 / 500000000) (-613585357 / 1000000000) (Real.log (693 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (377070991 / 1000000000) ≤ -Real.log (1024 / 1493) ∧
    -Real.log (1024 / 1493) ≤ (23566937 / 62500000) := by
  have h := checkLog_sound (w := (469 / 2517)) (n := 12)
    (lo := (377070991 / 1000000000)) (hi := (23566937 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1493 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1493 / 1024) = 1/(1024 / 1493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (377070991 / 1000000000) (23566937 / 62500000) (Real.log (1493 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1493 / 1024) = -Real.log (1024 / 1493) := by
    rw [show ((1493 / 1024) : ℝ) = ((1024 / 1493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (612503691 / 1000000000) ≤ -Real.log (555 / 1024) ∧
    -Real.log (555 / 1024) ≤ (153125923 / 250000000) := by
  have h := checkLog_sound (w := (469 / 1579)) (n := 12)
    (lo := (612503691 / 1000000000)) (hi := (153125923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 555) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 555) = 1/(555 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-153125923 / 250000000) (-612503691 / 1000000000) (Real.log (555 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (141448697 / 500000000) ≤ -Real.log (1000000 / 1326969) ∧
    -Real.log (1000000 / 1326969) ≤ (56579479 / 200000000) := by
  have h := checkLog_sound (w := (326969 / 2326969)) (n := 12)
    (lo := (141448697 / 500000000)) (hi := (56579479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1326969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1326969 / 1000000) = 1/(1000000 / 1326969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (141448697 / 500000000) (56579479 / 200000000) (Real.log (1326969 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1326969 / 1000000) = -Real.log (1000000 / 1326969) := by
    rw [show ((1326969 / 1000000) : ℝ) = ((1000000 / 1326969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (395963887 / 1000000000) ≤ -Real.log (673031 / 1000000) ∧
    -Real.log (673031 / 1000000) ≤ (24747743 / 62500000) := by
  have h := checkLog_sound (w := (326969 / 1673031)) (n := 12)
    (lo := (395963887 / 1000000000)) (hi := (24747743 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 673031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 673031) = 1/(673031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-24747743 / 62500000) (-395963887 / 1000000000) (Real.log (673031 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (283219881 / 1000000000) ≤ -Real.log (1000000 / 1327397) ∧
    -Real.log (1000000 / 1327397) ≤ (141609941 / 500000000) := by
  have h := checkLog_sound (w := (327397 / 2327397)) (n := 12)
    (lo := (283219881 / 1000000000)) (hi := (141609941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1327397 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1327397 / 1000000) = 1/(1000000 / 1327397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (283219881 / 1000000000) (141609941 / 500000000) (Real.log (1327397 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1327397 / 1000000) = -Real.log (1000000 / 1327397) := by
    rw [show ((1327397 / 1000000) : ℝ) = ((1000000 / 1327397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (396600019 / 1000000000) ≤ -Real.log (672603 / 1000000) ∧
    -Real.log (672603 / 1000000) ≤ (19830001 / 50000000) := by
  have h := checkLog_sound (w := (327397 / 1672603)) (n := 12)
    (lo := (396600019 / 1000000000)) (hi := (19830001 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 672603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 672603) = 1/(672603 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-19830001 / 50000000) (-396600019 / 1000000000) (Real.log (672603 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (213700707 / 1000000000) ≤ -Real.log (250000 / 309563) ∧
    -Real.log (250000 / 309563) ≤ (53425177 / 250000000) := by
  have h := checkLog_sound (w := (59563 / 559563)) (n := 12)
    (lo := (213700707 / 1000000000)) (hi := (53425177 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309563 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309563 / 250000) = 1/(250000 / 309563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (213700707 / 1000000000) (53425177 / 250000000) (Real.log (309563 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (309563 / 250000) = -Real.log (250000 / 309563) := by
    rw [show ((309563 / 250000) : ℝ) = ((250000 / 309563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (136069743 / 500000000) ≤ -Real.log (190437 / 250000) ∧
    -Real.log (190437 / 250000) ≤ (272139487 / 1000000000) := by
  have h := checkLog_sound (w := (59563 / 440437)) (n := 12)
    (lo := (136069743 / 500000000)) (hi := (272139487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 190437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 190437) = 1/(190437 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-272139487 / 1000000000) (-136069743 / 500000000) (Real.log (190437 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (13372999 / 62500000) ≤ -Real.log (1000000 / 1238583) ∧
    -Real.log (1000000 / 1238583) ≤ (42793597 / 200000000) := by
  have h := checkLog_sound (w := (238583 / 2238583)) (n := 12)
    (lo := (13372999 / 62500000)) (hi := (42793597 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1238583 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1238583 / 1000000) = 1/(1000000 / 1238583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (13372999 / 62500000) (42793597 / 200000000) (Real.log (1238583 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1238583 / 1000000) = -Real.log (1000000 / 1238583) := by
    rw [show ((1238583 / 1000000) : ℝ) = ((1000000 / 1238583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (272574107 / 1000000000) ≤ -Real.log (761417 / 1000000) ∧
    -Real.log (761417 / 1000000) ≤ (68143527 / 250000000) := by
  have h := checkLog_sound (w := (238583 / 1761417)) (n := 12)
    (lo := (272574107 / 1000000000)) (hi := (68143527 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 761417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 761417) = 1/(761417 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-68143527 / 250000000) (-272574107 / 1000000000) (Real.log (761417 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (339430641 / 500000000) ≤ -Real.log (250000000000 / 492907830397) ∧
    -Real.log (250000000000 / 492907830397) ≤ (678861283 / 1000000000) := by
  have h := checkLog_sound (w := (242907830397 / 742907830397)) (n := 12)
    (lo := (339430641 / 500000000)) (hi := (678861283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((492907830397 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(492907830397 / 250000000000) = 1/(250000000000 / 492907830397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (339430641 / 500000000) (678861283 / 1000000000) (Real.log (492907830397 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (492907830397 / 250000000000) = -Real.log (250000000000 / 492907830397) := by
    rw [show ((492907830397 / 250000000000) : ℝ) = ((250000000000 / 492907830397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (679819901 / 1000000000) ≤ -Real.log (50000000000 / 98676113547) ∧
    -Real.log (50000000000 / 98676113547) ≤ (339909951 / 500000000) := by
  have h := checkLog_sound (w := (48676113547 / 148676113547)) (n := 12)
    (lo := (679819901 / 1000000000)) (hi := (339909951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98676113547 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98676113547 / 50000000000) = 1/(50000000000 / 98676113547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (679819901 / 1000000000) (339909951 / 500000000) (Real.log (98676113547 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (98676113547 / 50000000000) = -Real.log (50000000000 / 98676113547) := by
    rw [show ((98676113547 / 50000000000) : ℝ) = ((50000000000 / 98676113547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (242920097 / 500000000) ≤ -Real.log (31250000000 / 50798131403) ∧
    -Real.log (31250000000 / 50798131403) ≤ (97168039 / 200000000) := by
  have h := checkLog_sound (w := (19548131403 / 82048131403)) (n := 12)
    (lo := (242920097 / 500000000)) (hi := (97168039 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50798131403 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50798131403 / 31250000000) = 1/(31250000000 / 50798131403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (242920097 / 500000000) (97168039 / 200000000) (Real.log (50798131403 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (50798131403 / 31250000000) = -Real.log (31250000000 / 50798131403) := by
    rw [show ((50798131403 / 31250000000) : ℝ) = ((31250000000 / 50798131403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (121635523 / 250000000) ≤ -Real.log (250000000000 / 406670392177) ∧
    -Real.log (250000000000 / 406670392177) ≤ (486542093 / 1000000000) := by
  have h := checkLog_sound (w := (156670392177 / 656670392177)) (n := 12)
    (lo := (121635523 / 250000000)) (hi := (486542093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((406670392177 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(406670392177 / 250000000000) = 1/(250000000000 / 406670392177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (121635523 / 250000000) (486542093 / 1000000000) (Real.log (406670392177 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (406670392177 / 250000000000) = -Real.log (250000000000 / 406670392177) := by
    rw [show ((406670392177 / 250000000000) : ℝ) = ((250000000000 / 406670392177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0374
