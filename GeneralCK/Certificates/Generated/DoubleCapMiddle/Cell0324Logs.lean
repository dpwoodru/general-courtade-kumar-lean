import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0324
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

theorem reflection_log_1_neg : (6821501 / 31250000) ≤ -Real.log (5120 / 6369) ∧
    -Real.log (5120 / 6369) ≤ (218288033 / 1000000000) := by
  have h := checkLog_sound (w := (1249 / 11489)) (n := 12)
    (lo := (6821501 / 31250000)) (hi := (218288033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6369 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6369 / 5120) = 1/(5120 / 6369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (6821501 / 31250000) (218288033 / 1000000000) (Real.log (6369 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6369 / 5120) = -Real.log (5120 / 6369) := by
    rw [show ((6369 / 5120) : ℝ) = ((5120 / 6369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (279641567 / 1000000000) ≤ -Real.log (3871 / 5120) ∧
    -Real.log (3871 / 5120) ≤ (8738799 / 31250000) := by
  have h := checkLog_sound (w := (1249 / 8991)) (n := 12)
    (lo := (279641567 / 1000000000)) (hi := (8738799 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3871) = 1/(3871 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-8738799 / 31250000) (-279641567 / 1000000000) (Real.log (3871 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (27256561 / 125000000) ≤ -Real.log (2048 / 2547) ∧
    -Real.log (2048 / 2547) ≤ (218052489 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 4595)) (n := 12)
    (lo := (27256561 / 125000000)) (hi := (218052489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2547 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2547 / 2048) = 1/(2048 / 2547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (27256561 / 125000000) (218052489 / 1000000000) (Real.log (2547 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2547 / 2048) = -Real.log (2048 / 2547) := by
    rw [show ((2547 / 2048) : ℝ) = ((2048 / 2547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (55850829 / 200000000) ≤ -Real.log (1549 / 2048) ∧
    -Real.log (1549 / 2048) ≤ (139627073 / 500000000) := by
  have h := checkLog_sound (w := (499 / 3597)) (n := 12)
    (lo := (55850829 / 200000000)) (hi := (139627073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1549) = 1/(1549 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-139627073 / 500000000) (-55850829 / 200000000) (Real.log (1549 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (397359429 / 1000000000) ≤ -Real.log (2560 / 3809) ∧
    -Real.log (2560 / 3809) ≤ (39735943 / 100000000) := by
  have h := checkLog_sound (w := (1249 / 6369)) (n := 12)
    (lo := (397359429 / 1000000000)) (hi := (39735943 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3809 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3809 / 2560) = 1/(2560 / 3809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (397359429 / 1000000000) (39735943 / 100000000) (Real.log (3809 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3809 / 2560) = -Real.log (2560 / 3809) := by
    rw [show ((3809 / 2560) : ℝ) = ((2560 / 3809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (669217053 / 1000000000) ≤ -Real.log (1311 / 2560) ∧
    -Real.log (1311 / 2560) ≤ (334608527 / 500000000) := by
  have h := checkLog_sound (w := (1249 / 3871)) (n := 12)
    (lo := (669217053 / 1000000000)) (hi := (334608527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1311) = 1/(1311 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-334608527 / 500000000) (-669217053 / 1000000000) (Real.log (1311 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (396965547 / 1000000000) ≤ -Real.log (1024 / 1523) ∧
    -Real.log (1024 / 1523) ≤ (99241387 / 250000000) := by
  have h := checkLog_sound (w := (499 / 2547)) (n := 12)
    (lo := (396965547 / 1000000000)) (hi := (99241387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1523 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1523 / 1024) = 1/(1024 / 1523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (396965547 / 1000000000) (99241387 / 250000000) (Real.log (1523 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1523 / 1024) = -Real.log (1024 / 1523) := by
    rw [show ((1523 / 1024) : ℝ) = ((1024 / 1523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (668073543 / 1000000000) ≤ -Real.log (525 / 1024) ∧
    -Real.log (525 / 1024) ≤ (83509193 / 125000000) := by
  have h := checkLog_sound (w := (499 / 1549)) (n := 12)
    (lo := (668073543 / 1000000000)) (hi := (83509193 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 525) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 525) = 1/(525 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-83509193 / 125000000) (-668073543 / 1000000000) (Real.log (525 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (298897197 / 1000000000) ≤ -Real.log (1000000 / 1348371) ∧
    -Real.log (1000000 / 1348371) ≤ (149448599 / 500000000) := by
  have h := checkLog_sound (w := (348371 / 2348371)) (n := 12)
    (lo := (298897197 / 1000000000)) (hi := (149448599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1348371 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1348371 / 1000000) = 1/(1000000 / 1348371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (298897197 / 1000000000) (149448599 / 500000000) (Real.log (1348371 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1348371 / 1000000) = -Real.log (1000000 / 1348371) := by
    rw [show ((1348371 / 1000000) : ℝ) = ((1000000 / 1348371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (428279897 / 1000000000) ≤ -Real.log (651629 / 1000000) ∧
    -Real.log (651629 / 1000000) ≤ (214139949 / 500000000) := by
  have h := checkLog_sound (w := (348371 / 1651629)) (n := 12)
    (lo := (428279897 / 1000000000)) (hi := (214139949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 651629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 651629) = 1/(651629 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-214139949 / 500000000) (-428279897 / 1000000000) (Real.log (651629 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (299216049 / 1000000000) ≤ -Real.log (1000000 / 1348801) ∧
    -Real.log (1000000 / 1348801) ≤ (5984321 / 20000000) := by
  have h := checkLog_sound (w := (348801 / 2348801)) (n := 12)
    (lo := (299216049 / 1000000000)) (hi := (5984321 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1348801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1348801 / 1000000) = 1/(1000000 / 1348801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (299216049 / 1000000000) (5984321 / 20000000) (Real.log (1348801 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1348801 / 1000000) = -Real.log (1000000 / 1348801) := by
    rw [show ((1348801 / 1000000) : ℝ) = ((1000000 / 1348801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (428939999 / 1000000000) ≤ -Real.log (651199 / 1000000) ∧
    -Real.log (651199 / 1000000) ≤ (21447 / 50000) := by
  have h := checkLog_sound (w := (348801 / 1651199)) (n := 12)
    (lo := (428939999 / 1000000000)) (hi := (21447 / 50000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 651199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 651199) = 1/(651199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-21447 / 50000) (-428939999 / 1000000000) (Real.log (651199 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (227051903 / 1000000000) ≤ -Real.log (200000 / 250979) ∧
    -Real.log (200000 / 250979) ≤ (1773843 / 7812500) := by
  have h := checkLog_sound (w := (50979 / 450979)) (n := 12)
    (lo := (227051903 / 1000000000)) (hi := (1773843 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250979 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250979 / 200000) = 1/(200000 / 250979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (227051903 / 1000000000) (1773843 / 7812500) (Real.log (250979 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (250979 / 200000) = -Real.log (200000 / 250979) := by
    rw [show ((250979 / 200000) : ℝ) = ((200000 / 250979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (29423013 / 100000000) ≤ -Real.log (149021 / 200000) ∧
    -Real.log (149021 / 200000) ≤ (294230131 / 1000000000) := by
  have h := checkLog_sound (w := (50979 / 349021)) (n := 12)
    (lo := (29423013 / 100000000)) (hi := (294230131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 149021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 149021) = 1/(149021 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-294230131 / 1000000000) (-29423013 / 100000000) (Real.log (149021 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (7103763 / 31250000) ≤ -Real.log (15625 / 19613) ∧
    -Real.log (15625 / 19613) ≤ (227320417 / 1000000000) := by
  have h := checkLog_sound (w := (1994 / 17619)) (n := 12)
    (lo := (7103763 / 31250000)) (hi := (227320417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19613 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19613 / 15625) = 1/(15625 / 19613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (7103763 / 31250000) (227320417 / 1000000000) (Real.log (19613 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (19613 / 15625) = -Real.log (15625 / 19613) := by
    rw [show ((19613 / 15625) : ℝ) = ((15625 / 19613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (147341259 / 500000000) ≤ -Real.log (11637 / 15625) ∧
    -Real.log (11637 / 15625) ≤ (294682519 / 1000000000) := by
  have h := checkLog_sound (w := (1994 / 13631)) (n := 12)
    (lo := (147341259 / 500000000)) (hi := (294682519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11637) = 1/(11637 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-294682519 / 1000000000) (-147341259 / 500000000) (Real.log (11637 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (363588547 / 500000000) ≤ -Real.log (62500000000 / 129326944473) ∧
    -Real.log (62500000000 / 129326944473) ≤ (90897137 / 125000000) := by
  have h := checkLog_sound (w := (4326944473 / 254326944473)) (n := 12)
    (lo := (17014957 / 500000000)) (hi := (6805983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129326944473 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(129326944473 / 125000000000) = 1/(62500000000 / 129326944473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (363588547 / 500000000) (90897137 / 125000000) (Real.log (129326944473 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (129326944473 / 62500000000) = -Real.log (62500000000 / 129326944473) := by
    rw [show ((129326944473 / 62500000000) : ℝ) = ((62500000000 / 129326944473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (728156049 / 1000000000) ≤ -Real.log (25000000000 / 51781444689) ∧
    -Real.log (25000000000 / 51781444689) ≤ (728156051 / 1000000000) := by
  have h := checkLog_sound (w := (1781444689 / 101781444689)) (n := 12)
    (lo := (35008869 / 1000000000)) (hi := (3500887 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51781444689 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(51781444689 / 50000000000) = 1/(25000000000 / 51781444689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (728156049 / 1000000000) (728156051 / 1000000000) (Real.log (51781444689 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (51781444689 / 25000000000) = -Real.log (25000000000 / 51781444689) := by
    rw [show ((51781444689 / 25000000000) : ℝ) = ((25000000000 / 51781444689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (260641017 / 500000000) ≤ -Real.log (250000000000 / 421046362593) ∧
    -Real.log (250000000000 / 421046362593) ≤ (104256407 / 200000000) := by
  have h := checkLog_sound (w := (171046362593 / 671046362593)) (n := 12)
    (lo := (260641017 / 500000000)) (hi := (104256407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421046362593 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421046362593 / 250000000000) = 1/(250000000000 / 421046362593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (260641017 / 500000000) (104256407 / 200000000) (Real.log (421046362593 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (421046362593 / 250000000000) = -Real.log (250000000000 / 421046362593) := by
    rw [show ((421046362593 / 250000000000) : ℝ) = ((250000000000 / 421046362593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (261001467 / 500000000) ≤ -Real.log (250000000000 / 421350004297) ∧
    -Real.log (250000000000 / 421350004297) ≤ (104400587 / 200000000) := by
  have h := checkLog_sound (w := (171350004297 / 671350004297)) (n := 12)
    (lo := (261001467 / 500000000)) (hi := (104400587 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421350004297 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421350004297 / 250000000000) = 1/(250000000000 / 421350004297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (261001467 / 500000000) (104400587 / 200000000) (Real.log (421350004297 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (421350004297 / 250000000000) = -Real.log (250000000000 / 421350004297) := by
    rw [show ((421350004297 / 250000000000) : ℝ) = ((250000000000 / 421350004297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0324
