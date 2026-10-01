import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell085
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

theorem reflection_log_1_neg : (2626647 / 10000000) ≤ -Real.log (2560 / 3329) ∧
    -Real.log (2560 / 3329) ≤ (262664701 / 1000000000) := by
  have h := checkLog_sound (w := (769 / 5889)) (n := 12)
    (lo := (2626647 / 10000000)) (hi := (262664701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3329 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3329 / 2560) = 1/(2560 / 3329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (2626647 / 10000000) (262664701 / 1000000000) (Real.log (3329 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3329 / 2560) = -Real.log (2560 / 3329) := by
    rw [show ((3329 / 2560) : ℝ) = ((2560 / 3329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (71446627 / 200000000) ≤ -Real.log (1791 / 2560) ∧
    -Real.log (1791 / 2560) ≤ (22327071 / 62500000) := by
  have h := checkLog_sound (w := (769 / 4351)) (n := 12)
    (lo := (71446627 / 200000000)) (hi := (22327071 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1791) = 1/(1791 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-22327071 / 62500000) (-71446627 / 200000000) (Real.log (1791 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (65553503 / 250000000) ≤ -Real.log (1024 / 1331) ∧
    -Real.log (1024 / 1331) ≤ (262214013 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 2355)) (n := 12)
    (lo := (65553503 / 250000000)) (hi := (262214013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1331 / 1024) = 1/(1024 / 1331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (65553503 / 250000000) (262214013 / 1000000000) (Real.log (1331 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1331 / 1024) = -Real.log (1024 / 1331) := by
    rw [show ((1331 / 1024) : ℝ) = ((1024 / 1331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (89098991 / 250000000) ≤ -Real.log (717 / 1024) ∧
    -Real.log (717 / 1024) ≤ (71279193 / 200000000) := by
  have h := checkLog_sound (w := (307 / 1741)) (n := 12)
    (lo := (89098991 / 250000000)) (hi := (71279193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 717) = 1/(717 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-71279193 / 200000000) (-89098991 / 250000000) (Real.log (717 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (192946577 / 1000000000) ≤ -Real.log (500000 / 606409) ∧
    -Real.log (500000 / 606409) ≤ (96473289 / 500000000) := by
  have h := checkLog_sound (w := (106409 / 1106409)) (n := 12)
    (lo := (192946577 / 1000000000)) (hi := (96473289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606409 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606409 / 500000) = 1/(500000 / 606409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (192946577 / 1000000000) (96473289 / 500000000) (Real.log (606409 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (606409 / 500000) = -Real.log (500000 / 606409) := by
    rw [show ((606409 / 500000) : ℝ) = ((500000 / 606409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (239295799 / 1000000000) ≤ -Real.log (393591 / 500000) ∧
    -Real.log (393591 / 500000) ≤ (1196479 / 5000000) := by
  have h := checkLog_sound (w := (106409 / 893591)) (n := 12)
    (lo := (239295799 / 1000000000)) (hi := (1196479 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393591) = 1/(393591 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1196479 / 5000000) (-239295799 / 1000000000) (Real.log (393591 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (96646821 / 500000000) ≤ -Real.log (1000000 / 1213239) ∧
    -Real.log (1000000 / 1213239) ≤ (193293643 / 1000000000) := by
  have h := checkLog_sound (w := (213239 / 2213239)) (n := 12)
    (lo := (96646821 / 500000000)) (hi := (193293643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213239 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1213239 / 1000000) = 1/(1000000 / 1213239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (96646821 / 500000000) (193293643 / 1000000000) (Real.log (1213239 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1213239 / 1000000) = -Real.log (1000000 / 1213239) := by
    rw [show ((1213239 / 1000000) : ℝ) = ((1000000 / 1213239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (239830761 / 1000000000) ≤ -Real.log (786761 / 1000000) ∧
    -Real.log (786761 / 1000000) ≤ (119915381 / 500000000) := by
  have h := checkLog_sound (w := (213239 / 1786761)) (n := 12)
    (lo := (239830761 / 1000000000)) (hi := (119915381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 786761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 786761) = 1/(786761 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-119915381 / 500000000) (-239830761 / 1000000000) (Real.log (786761 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35461247 / 250000000) ≤ -Real.log (500000 / 576199) ∧
    -Real.log (500000 / 576199) ≤ (141844989 / 1000000000) := by
  have h := checkLog_sound (w := (76199 / 1076199)) (n := 12)
    (lo := (35461247 / 250000000)) (hi := (141844989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576199 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(576199 / 500000) = 1/(500000 / 576199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35461247 / 250000000) (141844989 / 1000000000) (Real.log (576199 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (576199 / 500000) = -Real.log (500000 / 576199) := by
    rw [show ((576199 / 500000) : ℝ) = ((500000 / 576199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (41336023 / 250000000) ≤ -Real.log (423801 / 500000) ∧
    -Real.log (423801 / 500000) ≤ (165344093 / 1000000000) := by
  have h := checkLog_sound (w := (76199 / 923801)) (n := 12)
    (lo := (41336023 / 250000000)) (hi := (165344093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 423801) = 1/(423801 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-165344093 / 1000000000) (-41336023 / 250000000) (Real.log (423801 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (142113089 / 1000000000) ≤ -Real.log (1000000 / 1152707) ∧
    -Real.log (1000000 / 1152707) ≤ (14211309 / 100000000) := by
  have h := checkLog_sound (w := (152707 / 2152707)) (n := 12)
    (lo := (142113089 / 1000000000)) (hi := (14211309 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152707 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1152707 / 1000000) = 1/(1000000 / 1152707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (142113089 / 1000000000) (14211309 / 100000000) (Real.log (1152707 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1152707 / 1000000) = -Real.log (1000000 / 1152707) := by
    rw [show ((1152707 / 1000000) : ℝ) = ((1000000 / 1152707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (165708717 / 1000000000) ≤ -Real.log (847293 / 1000000) ∧
    -Real.log (847293 / 1000000) ≤ (82854359 / 500000000) := by
  have h := checkLog_sound (w := (152707 / 1847293)) (n := 12)
    (lo := (165708717 / 1000000000)) (hi := (82854359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 847293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 847293) = 1/(847293 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-82854359 / 500000000) (-165708717 / 1000000000) (Real.log (847293 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (618609977 / 1000000000) ≤ -Real.log (500000000000 / 928172942817) ∧
    -Real.log (500000000000 / 928172942817) ≤ (309304989 / 500000000) := by
  have h := checkLog_sound (w := (428172942817 / 1428172942817)) (n := 12)
    (lo := (618609977 / 1000000000)) (hi := (309304989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((928172942817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(928172942817 / 500000000000) = 1/(500000000000 / 928172942817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (618609977 / 1000000000) (309304989 / 500000000) (Real.log (928172942817 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (928172942817 / 500000000000) = -Real.log (500000000000 / 928172942817) := by
    rw [show ((928172942817 / 500000000000) : ℝ) = ((500000000000 / 928172942817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (123979567 / 200000000) ≤ -Real.log (500000000000 / 929369067561) ∧
    -Real.log (500000000000 / 929369067561) ≤ (154974459 / 250000000) := by
  have h := checkLog_sound (w := (429369067561 / 1429369067561)) (n := 12)
    (lo := (123979567 / 200000000)) (hi := (154974459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((929369067561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(929369067561 / 500000000000) = 1/(500000000000 / 929369067561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (123979567 / 200000000) (154974459 / 250000000) (Real.log (929369067561 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (929369067561 / 500000000000) = -Real.log (500000000000 / 929369067561) := by
    rw [show ((929369067561 / 500000000000) : ℝ) = ((500000000000 / 929369067561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (54030297 / 125000000) ≤ -Real.log (250000000000 / 385177125493) ∧
    -Real.log (250000000000 / 385177125493) ≤ (432242377 / 1000000000) := by
  have h := checkLog_sound (w := (135177125493 / 635177125493)) (n := 12)
    (lo := (54030297 / 125000000)) (hi := (432242377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((385177125493 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(385177125493 / 250000000000) = 1/(250000000000 / 385177125493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (54030297 / 125000000) (432242377 / 1000000000) (Real.log (385177125493 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (385177125493 / 250000000000) = -Real.log (250000000000 / 385177125493) := by
    rw [show ((385177125493 / 250000000000) : ℝ) = ((250000000000 / 385177125493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (108281101 / 250000000) ≤ -Real.log (50000000000 / 77103402431) ∧
    -Real.log (50000000000 / 77103402431) ≤ (86624881 / 200000000) := by
  have h := checkLog_sound (w := (27103402431 / 127103402431)) (n := 12)
    (lo := (108281101 / 250000000)) (hi := (86624881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77103402431 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77103402431 / 50000000000) = 1/(50000000000 / 77103402431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (108281101 / 250000000) (86624881 / 200000000) (Real.log (77103402431 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (77103402431 / 50000000000) = -Real.log (50000000000 / 77103402431) := by
    rw [show ((77103402431 / 50000000000) : ℝ) = ((50000000000 / 77103402431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (307189081 / 1000000000) ≤ -Real.log (3125000000 / 4248743809) ∧
    -Real.log (3125000000 / 4248743809) ≤ (153594541 / 500000000) := by
  have h := checkLog_sound (w := (1123743809 / 7373743809)) (n := 12)
    (lo := (307189081 / 1000000000)) (hi := (153594541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4248743809 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4248743809 / 3125000000) = 1/(3125000000 / 4248743809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (307189081 / 1000000000) (153594541 / 500000000) (Real.log (4248743809 / 3125000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4248743809 / 3125000000) = -Real.log (3125000000 / 4248743809) := by
    rw [show ((4248743809 / 3125000000) : ℝ) = ((3125000000 / 4248743809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (153910903 / 500000000) ≤ -Real.log (500000000000 / 680229271339) ∧
    -Real.log (500000000000 / 680229271339) ≤ (307821807 / 1000000000) := by
  have h := checkLog_sound (w := (180229271339 / 1180229271339)) (n := 12)
    (lo := (153910903 / 500000000)) (hi := (307821807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((680229271339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(680229271339 / 500000000000) = 1/(500000000000 / 680229271339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (153910903 / 500000000) (307821807 / 1000000000) (Real.log (680229271339 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (680229271339 / 500000000000) = -Real.log (500000000000 / 680229271339) := by
    rw [show ((680229271339 / 500000000000) : ℝ) = ((500000000000 / 680229271339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5898907 / 250000000) ≤ -Real.log (976680572151 / 1000000000000) ∧
    -Real.log (976680572151 / 1000000000000) ≤ (23595629 / 1000000000) := by
  have h := checkLog_sound (w := (23319427849 / 1976680572151)) (n := 12)
    (lo := (5898907 / 250000000)) (hi := (23595629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976680572151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976680572151) = 1/(976680572151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-23595629 / 1000000000) (-5898907 / 250000000) (Real.log (976680572151 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (734347 / 31250000) ≤ -Real.log (244193712399 / 250000000000) ∧
    -Real.log (244193712399 / 250000000000) ≤ (4699821 / 200000000) := by
  have h := checkLog_sound (w := (5806287601 / 494193712399)) (n := 12)
    (lo := (734347 / 31250000)) (hi := (4699821 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244193712399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244193712399) = 1/(244193712399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4699821 / 200000000) (-734347 / 31250000) (Real.log (244193712399 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell085
