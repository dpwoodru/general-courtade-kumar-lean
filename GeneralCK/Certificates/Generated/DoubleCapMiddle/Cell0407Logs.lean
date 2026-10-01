import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0407
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

theorem reflection_log_1_neg : (198546637 / 1000000000) ≤ -Real.log (10240 / 12489) ∧
    -Real.log (10240 / 12489) ≤ (99273319 / 500000000) := by
  have h := checkLog_sound (w := (2249 / 22729)) (n := 12)
    (lo := (198546637 / 1000000000)) (hi := (99273319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12489 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12489 / 10240) = 1/(10240 / 12489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (198546637 / 1000000000) (99273319 / 500000000) (Real.log (12489 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12489 / 10240) = -Real.log (10240 / 12489) := by
    rw [show ((12489 / 10240) : ℝ) = ((10240 / 12489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (247985711 / 1000000000) ≤ -Real.log (7991 / 10240) ∧
    -Real.log (7991 / 10240) ≤ (15499107 / 62500000) := by
  have h := checkLog_sound (w := (2249 / 18231)) (n := 12)
    (lo := (247985711 / 1000000000)) (hi := (15499107 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7991) = 1/(7991 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-15499107 / 62500000) (-247985711 / 1000000000) (Real.log (7991 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (198306397 / 1000000000) ≤ -Real.log (5120 / 6243) ∧
    -Real.log (5120 / 6243) ≤ (99153199 / 500000000) := by
  have h := checkLog_sound (w := (1123 / 11363)) (n := 12)
    (lo := (198306397 / 1000000000)) (hi := (99153199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6243 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6243 / 5120) = 1/(5120 / 6243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (198306397 / 1000000000) (99153199 / 500000000) (Real.log (6243 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6243 / 5120) = -Real.log (5120 / 6243) := by
    rw [show ((6243 / 5120) : ℝ) = ((5120 / 6243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (247610359 / 1000000000) ≤ -Real.log (3997 / 5120) ∧
    -Real.log (3997 / 5120) ≤ (6190259 / 25000000) := by
  have h := checkLog_sound (w := (1123 / 9117)) (n := 12)
    (lo := (247610359 / 1000000000)) (hi := (6190259 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3997) = 1/(3997 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6190259 / 25000000) (-247610359 / 1000000000) (Real.log (3997 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (91031893 / 250000000) ≤ -Real.log (5120 / 7369) ∧
    -Real.log (5120 / 7369) ≤ (364127573 / 1000000000) := by
  have h := checkLog_sound (w := (2249 / 12489)) (n := 12)
    (lo := (91031893 / 250000000)) (hi := (364127573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7369 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7369 / 5120) = 1/(5120 / 7369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (91031893 / 250000000) (364127573 / 1000000000) (Real.log (7369 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7369 / 5120) = -Real.log (5120 / 7369) := by
    rw [show ((7369 / 5120) : ℝ) = ((5120 / 7369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (578494037 / 1000000000) ≤ -Real.log (2871 / 5120) ∧
    -Real.log (2871 / 5120) ≤ (289247019 / 500000000) := by
  have h := checkLog_sound (w := (2249 / 7991)) (n := 12)
    (lo := (578494037 / 1000000000)) (hi := (289247019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2871) = 1/(2871 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-289247019 / 500000000) (-578494037 / 1000000000) (Real.log (2871 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (181860189 / 500000000) ≤ -Real.log (2560 / 3683) ∧
    -Real.log (2560 / 3683) ≤ (363720379 / 1000000000) := by
  have h := checkLog_sound (w := (1123 / 6243)) (n := 12)
    (lo := (181860189 / 500000000)) (hi := (363720379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3683 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3683 / 2560) = 1/(2560 / 3683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (181860189 / 500000000) (363720379 / 1000000000) (Real.log (3683 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3683 / 2560) = -Real.log (2560 / 3683) := by
    rw [show ((3683 / 2560) : ℝ) = ((2560 / 3683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (577449651 / 1000000000) ≤ -Real.log (1437 / 2560) ∧
    -Real.log (1437 / 2560) ≤ (144362413 / 250000000) := by
  have h := checkLog_sound (w := (1123 / 3997)) (n := 12)
    (lo := (577449651 / 1000000000)) (hi := (144362413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1437) = 1/(1437 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-144362413 / 250000000) (-577449651 / 1000000000) (Real.log (1437 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (34029423 / 125000000) ≤ -Real.log (15625 / 20514) ∧
    -Real.log (15625 / 20514) ≤ (54447077 / 200000000) := by
  have h := checkLog_sound (w := (4889 / 36139)) (n := 12)
    (lo := (34029423 / 125000000)) (hi := (54447077 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20514 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20514 / 15625) = 1/(15625 / 20514) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (34029423 / 125000000) (54447077 / 200000000) (Real.log (20514 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (20514 / 15625) = -Real.log (15625 / 20514) := by
    rw [show ((20514 / 15625) : ℝ) = ((15625 / 20514) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (75053923 / 200000000) ≤ -Real.log (10736 / 15625) ∧
    -Real.log (10736 / 15625) ≤ (23454351 / 62500000) := by
  have h := checkLog_sound (w := (4889 / 26361)) (n := 12)
    (lo := (75053923 / 200000000)) (hi := (23454351 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10736) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 10736) = 1/(10736 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-23454351 / 62500000) (-75053923 / 200000000) (Real.log (10736 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136280283 / 500000000) ≤ -Real.log (1000000 / 1313323) ∧
    -Real.log (1000000 / 1313323) ≤ (272560567 / 1000000000) := by
  have h := checkLog_sound (w := (313323 / 2313323)) (n := 12)
    (lo := (136280283 / 500000000)) (hi := (272560567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1313323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1313323 / 1000000) = 1/(1000000 / 1313323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136280283 / 500000000) (272560567 / 1000000000) (Real.log (1313323 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1313323 / 1000000) = -Real.log (1000000 / 1313323) := by
    rw [show ((1313323 / 1000000) : ℝ) = ((1000000 / 1313323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (375891257 / 1000000000) ≤ -Real.log (686677 / 1000000) ∧
    -Real.log (686677 / 1000000) ≤ (187945629 / 500000000) := by
  have h := checkLog_sound (w := (313323 / 1686677)) (n := 12)
    (lo := (375891257 / 1000000000)) (hi := (187945629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 686677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 686677) = 1/(686677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-187945629 / 500000000) (-375891257 / 1000000000) (Real.log (686677 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (204909517 / 1000000000) ≤ -Real.log (500000 / 613707) ∧
    -Real.log (500000 / 613707) ≤ (102454759 / 500000000) := by
  have h := checkLog_sound (w := (113707 / 1113707)) (n := 12)
    (lo := (204909517 / 1000000000)) (hi := (102454759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613707 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613707 / 500000) = 1/(500000 / 613707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (204909517 / 1000000000) (102454759 / 500000000) (Real.log (613707 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (613707 / 500000) = -Real.log (500000 / 613707) := by
    rw [show ((613707 / 500000) : ℝ) = ((500000 / 613707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (258011949 / 1000000000) ≤ -Real.log (386293 / 500000) ∧
    -Real.log (386293 / 500000) ≤ (5160239 / 20000000) := by
  have h := checkLog_sound (w := (113707 / 886293)) (n := 12)
    (lo := (258011949 / 1000000000)) (hi := (5160239 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386293) = 1/(386293 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-5160239 / 20000000) (-258011949 / 1000000000) (Real.log (386293 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (205176709 / 1000000000) ≤ -Real.log (500000 / 613871) ∧
    -Real.log (500000 / 613871) ≤ (20517671 / 100000000) := by
  have h := checkLog_sound (w := (113871 / 1113871)) (n := 12)
    (lo := (205176709 / 1000000000)) (hi := (20517671 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613871 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613871 / 500000) = 1/(500000 / 613871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (205176709 / 1000000000) (20517671 / 100000000) (Real.log (613871 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (613871 / 500000) = -Real.log (500000 / 613871) := by
    rw [show ((613871 / 500000) : ℝ) = ((500000 / 613871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (258436587 / 1000000000) ≤ -Real.log (386129 / 500000) ∧
    -Real.log (386129 / 500000) ≤ (64609147 / 250000000) := by
  have h := checkLog_sound (w := (113871 / 886129)) (n := 12)
    (lo := (258436587 / 1000000000)) (hi := (64609147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386129) = 1/(386129 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-64609147 / 250000000) (-258436587 / 1000000000) (Real.log (386129 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (647504999 / 1000000000) ≤ -Real.log (125000000000 / 238845938897) ∧
    -Real.log (125000000000 / 238845938897) ≤ (129501 / 200000) := by
  have h := checkLog_sound (w := (113845938897 / 363845938897)) (n := 12)
    (lo := (647504999 / 1000000000)) (hi := (129501 / 200000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238845938897 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(238845938897 / 125000000000) = 1/(125000000000 / 238845938897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (647504999 / 1000000000) (129501 / 200000) (Real.log (238845938897 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (238845938897 / 125000000000) = -Real.log (125000000000 / 238845938897) := by
    rw [show ((238845938897 / 125000000000) : ℝ) = ((125000000000 / 238845938897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (40528239 / 62500000) ≤ -Real.log (500000000000 / 956288764587) ∧
    -Real.log (500000000000 / 956288764587) ≤ (25938073 / 40000000) := by
  have h := checkLog_sound (w := (456288764587 / 1456288764587)) (n := 12)
    (lo := (40528239 / 62500000)) (hi := (25938073 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((956288764587 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(956288764587 / 500000000000) = 1/(500000000000 / 956288764587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (40528239 / 62500000) (25938073 / 40000000) (Real.log (956288764587 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (956288764587 / 500000000000) = -Real.log (500000000000 / 956288764587) := by
    rw [show ((956288764587 / 500000000000) : ℝ) = ((500000000000 / 956288764587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (231460733 / 500000000) ≤ -Real.log (500000000000 / 794354285477) ∧
    -Real.log (500000000000 / 794354285477) ≤ (462921467 / 1000000000) := by
  have h := checkLog_sound (w := (294354285477 / 1294354285477)) (n := 12)
    (lo := (231460733 / 500000000)) (hi := (462921467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794354285477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794354285477 / 500000000000) = 1/(500000000000 / 794354285477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (231460733 / 500000000) (462921467 / 1000000000) (Real.log (794354285477 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (794354285477 / 500000000000) = -Real.log (500000000000 / 794354285477) := by
    rw [show ((794354285477 / 500000000000) : ℝ) = ((500000000000 / 794354285477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (463613297 / 1000000000) ≤ -Real.log (250000000000 / 397452017331) ∧
    -Real.log (250000000000 / 397452017331) ≤ (231806649 / 500000000) := by
  have h := checkLog_sound (w := (147452017331 / 647452017331)) (n := 12)
    (lo := (463613297 / 1000000000)) (hi := (231806649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397452017331 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397452017331 / 250000000000) = 1/(250000000000 / 397452017331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (463613297 / 1000000000) (231806649 / 500000000) (Real.log (397452017331 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (397452017331 / 250000000000) = -Real.log (250000000000 / 397452017331) := by
    rw [show ((397452017331 / 250000000000) : ℝ) = ((250000000000 / 397452017331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0407
