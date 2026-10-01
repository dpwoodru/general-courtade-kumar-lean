import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0366
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

theorem reflection_log_1_neg : (104173561 / 500000000) ≤ -Real.log (2560 / 3153) ∧
    -Real.log (2560 / 3153) ≤ (208347123 / 1000000000) := by
  have h := checkLog_sound (w := (593 / 5713)) (n := 12)
    (lo := (104173561 / 500000000)) (hi := (208347123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3153 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3153 / 2560) = 1/(2560 / 3153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (104173561 / 500000000) (208347123 / 1000000000) (Real.log (3153 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3153 / 2560) = -Real.log (2560 / 3153) := by
    rw [show ((3153 / 2560) : ℝ) = ((2560 / 3153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (263497719 / 1000000000) ≤ -Real.log (1967 / 2560) ∧
    -Real.log (1967 / 2560) ≤ (6587443 / 25000000) := by
  have h := checkLog_sound (w := (593 / 4527)) (n := 12)
    (lo := (263497719 / 1000000000)) (hi := (6587443 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1967) = 1/(1967 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6587443 / 25000000) (-263497719 / 1000000000) (Real.log (1967 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8324369 / 40000000) ≤ -Real.log (10240 / 12609) ∧
    -Real.log (10240 / 12609) ≤ (104054613 / 500000000) := by
  have h := checkLog_sound (w := (2369 / 22849)) (n := 12)
    (lo := (8324369 / 40000000)) (hi := (104054613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12609 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12609 / 10240) = 1/(10240 / 12609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8324369 / 40000000) (104054613 / 500000000) (Real.log (12609 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12609 / 10240) = -Real.log (10240 / 12609) := by
    rw [show ((12609 / 10240) : ℝ) = ((10240 / 12609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (526233 / 2000000) ≤ -Real.log (7871 / 10240) ∧
    -Real.log (7871 / 10240) ≤ (263116501 / 1000000000) := by
  have h := checkLog_sound (w := (2369 / 18111)) (n := 12)
    (lo := (526233 / 2000000)) (hi := (263116501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7871) = 1/(7871 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-263116501 / 1000000000) (-526233 / 2000000) (Real.log (7871 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (76136269 / 200000000) ≤ -Real.log (1280 / 1873) ∧
    -Real.log (1280 / 1873) ≤ (190340673 / 500000000) := by
  have h := checkLog_sound (w := (593 / 3153)) (n := 12)
    (lo := (76136269 / 200000000)) (hi := (190340673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1873 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1873 / 1280) = 1/(1280 / 1873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (76136269 / 200000000) (190340673 / 500000000) (Real.log (1873 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1873 / 1280) = -Real.log (1280 / 1873) := by
    rw [show ((1873 / 1280) : ℝ) = ((1280 / 1873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (77785133 / 125000000) ≤ -Real.log (687 / 1280) ∧
    -Real.log (687 / 1280) ≤ (124456213 / 200000000) := by
  have h := checkLog_sound (w := (593 / 1967)) (n := 12)
    (lo := (77785133 / 125000000)) (hi := (124456213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 687) = 1/(687 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-124456213 / 200000000) (-77785133 / 125000000) (Real.log (687 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (190140419 / 500000000) ≤ -Real.log (5120 / 7489) ∧
    -Real.log (5120 / 7489) ≤ (380280839 / 1000000000) := by
  have h := checkLog_sound (w := (2369 / 12609)) (n := 12)
    (lo := (190140419 / 500000000)) (hi := (380280839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7489 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7489 / 5120) = 1/(5120 / 7489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (190140419 / 500000000) (380280839 / 1000000000) (Real.log (7489 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7489 / 5120) = -Real.log (5120 / 7489) := by
    rw [show ((7489 / 5120) : ℝ) = ((5120 / 7489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (621189957 / 1000000000) ≤ -Real.log (2751 / 5120) ∧
    -Real.log (2751 / 5120) ≤ (310594979 / 500000000) := by
  have h := checkLog_sound (w := (2369 / 7871)) (n := 12)
    (lo := (621189957 / 1000000000)) (hi := (310594979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2751) = 1/(2751 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-310594979 / 500000000) (-621189957 / 1000000000) (Real.log (2751 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2283753 / 8000000) ≤ -Real.log (500000 / 665193) ∧
    -Real.log (500000 / 665193) ≤ (142734563 / 500000000) := by
  have h := checkLog_sound (w := (165193 / 1165193)) (n := 12)
    (lo := (2283753 / 8000000)) (hi := (142734563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665193 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665193 / 500000) = 1/(500000 / 665193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2283753 / 8000000) (142734563 / 500000000) (Real.log (665193 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (665193 / 500000) = -Real.log (500000 / 665193) := by
    rw [show ((665193 / 500000) : ℝ) = ((500000 / 665193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (100263463 / 250000000) ≤ -Real.log (334807 / 500000) ∧
    -Real.log (334807 / 500000) ≤ (401053853 / 1000000000) := by
  have h := checkLog_sound (w := (165193 / 834807)) (n := 12)
    (lo := (100263463 / 250000000)) (hi := (401053853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 334807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 334807) = 1/(334807 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-401053853 / 1000000000) (-100263463 / 250000000) (Real.log (334807 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17861971 / 62500000) ≤ -Real.log (200000 / 266163) ∧
    -Real.log (200000 / 266163) ≤ (285791537 / 1000000000) := by
  have h := checkLog_sound (w := (66163 / 466163)) (n := 12)
    (lo := (17861971 / 62500000)) (hi := (285791537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((266163 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(266163 / 200000) = 1/(200000 / 266163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17861971 / 62500000) (285791537 / 1000000000) (Real.log (266163 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (266163 / 200000) = -Real.log (200000 / 266163) := by
    rw [show ((266163 / 200000) : ℝ) = ((200000 / 266163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (100423681 / 250000000) ≤ -Real.log (133837 / 200000) ∧
    -Real.log (133837 / 200000) ≤ (16067789 / 40000000) := by
  have h := checkLog_sound (w := (66163 / 333837)) (n := 12)
    (lo := (100423681 / 250000000)) (hi := (16067789 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 133837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 133837) = 1/(133837 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-16067789 / 40000000) (-100423681 / 250000000) (Real.log (133837 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (215833699 / 1000000000) ≤ -Real.log (15625 / 19389) ∧
    -Real.log (15625 / 19389) ≤ (2158337 / 10000000) := by
  have h := checkLog_sound (w := (1882 / 17507)) (n := 12)
    (lo := (215833699 / 1000000000)) (hi := (2158337 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19389 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19389 / 15625) = 1/(15625 / 19389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (215833699 / 1000000000) (2158337 / 10000000) (Real.log (19389 / 15625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (19389 / 15625) = -Real.log (15625 / 19389) := by
    rw [show ((19389 / 15625) : ℝ) = ((15625 / 19389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (34452061 / 125000000) ≤ -Real.log (11861 / 15625) ∧
    -Real.log (11861 / 15625) ≤ (275616489 / 1000000000) := by
  have h := checkLog_sound (w := (1882 / 13743)) (n := 12)
    (lo := (34452061 / 125000000)) (hi := (275616489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11861) = 1/(11861 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-275616489 / 1000000000) (-34452061 / 125000000) (Real.log (11861 / 15625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (54025303 / 250000000) ≤ -Real.log (250000 / 310307) ∧
    -Real.log (250000 / 310307) ≤ (216101213 / 1000000000) := by
  have h := checkLog_sound (w := (60307 / 560307)) (n := 12)
    (lo := (54025303 / 250000000)) (hi := (216101213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310307 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310307 / 250000) = 1/(250000 / 310307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (54025303 / 250000000) (216101213 / 1000000000) (Real.log (310307 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (310307 / 250000) = -Real.log (250000 / 310307) := by
    rw [show ((310307 / 250000) : ℝ) = ((250000 / 310307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (276053941 / 1000000000) ≤ -Real.log (189693 / 250000) ∧
    -Real.log (189693 / 250000) ≤ (138026971 / 500000000) := by
  have h := checkLog_sound (w := (60307 / 439693)) (n := 12)
    (lo := (276053941 / 1000000000)) (hi := (138026971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 189693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 189693) = 1/(189693 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-138026971 / 500000000) (-276053941 / 1000000000) (Real.log (189693 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (686522977 / 1000000000) ≤ -Real.log (500000000000 / 993397688817) ∧
    -Real.log (500000000000 / 993397688817) ≤ (343261489 / 500000000) := by
  have h := checkLog_sound (w := (493397688817 / 1493397688817)) (n := 12)
    (lo := (686522977 / 1000000000)) (hi := (343261489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((993397688817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(993397688817 / 500000000000) = 1/(500000000000 / 993397688817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (686522977 / 1000000000) (343261489 / 500000000) (Real.log (993397688817 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (993397688817 / 500000000000) = -Real.log (500000000000 / 993397688817) := by
    rw [show ((993397688817 / 500000000000) : ℝ) = ((500000000000 / 993397688817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (687486261 / 1000000000) ≤ -Real.log (50000000000 / 99435507371) ∧
    -Real.log (50000000000 / 99435507371) ≤ (343743131 / 500000000) := by
  have h := checkLog_sound (w := (49435507371 / 149435507371)) (n := 12)
    (lo := (687486261 / 1000000000)) (hi := (343743131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99435507371 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99435507371 / 50000000000) = 1/(50000000000 / 99435507371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (687486261 / 1000000000) (343743131 / 500000000) (Real.log (99435507371 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (99435507371 / 50000000000) = -Real.log (50000000000 / 99435507371) := by
    rw [show ((99435507371 / 50000000000) : ℝ) = ((50000000000 / 99435507371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (491450187 / 1000000000) ≤ -Real.log (250000000000 / 408671275609) ∧
    -Real.log (250000000000 / 408671275609) ≤ (122862547 / 250000000) := by
  have h := checkLog_sound (w := (158671275609 / 658671275609)) (n := 12)
    (lo := (491450187 / 1000000000)) (hi := (122862547 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((408671275609 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(408671275609 / 250000000000) = 1/(250000000000 / 408671275609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (491450187 / 1000000000) (122862547 / 250000000) (Real.log (408671275609 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (408671275609 / 250000000000) = -Real.log (250000000000 / 408671275609) := by
    rw [show ((408671275609 / 250000000000) : ℝ) = ((250000000000 / 408671275609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (246077577 / 500000000) ≤ -Real.log (500000000000 / 817918953257) ∧
    -Real.log (500000000000 / 817918953257) ≤ (98431031 / 200000000) := by
  have h := checkLog_sound (w := (317918953257 / 1317918953257)) (n := 12)
    (lo := (246077577 / 500000000)) (hi := (98431031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817918953257 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817918953257 / 500000000000) = 1/(500000000000 / 817918953257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (246077577 / 500000000) (98431031 / 200000000) (Real.log (817918953257 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (817918953257 / 500000000000) = -Real.log (500000000000 / 817918953257) := by
    rw [show ((817918953257 / 500000000000) : ℝ) = ((500000000000 / 817918953257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0366
