import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0327
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

theorem reflection_log_1_neg : (43516247 / 200000000) ≤ -Real.log (10240 / 12729) ∧
    -Real.log (10240 / 12729) ≤ (54395309 / 250000000) := by
  have h := checkLog_sound (w := (2489 / 22969)) (n := 12)
    (lo := (43516247 / 200000000)) (hi := (54395309 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12729 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12729 / 10240) = 1/(10240 / 12729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (43516247 / 200000000) (54395309 / 250000000) (Real.log (12729 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12729 / 10240) = -Real.log (10240 / 12729) := by
    rw [show ((12729 / 10240) : ℝ) = ((10240 / 12729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (34809969 / 125000000) ≤ -Real.log (7751 / 10240) ∧
    -Real.log (7751 / 10240) ≤ (278479753 / 1000000000) := by
  have h := checkLog_sound (w := (2489 / 17991)) (n := 12)
    (lo := (34809969 / 125000000)) (hi := (278479753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7751) = 1/(7751 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-278479753 / 1000000000) (-34809969 / 125000000) (Real.log (7751 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8693821 / 40000000) ≤ -Real.log (5120 / 6363) ∧
    -Real.log (5120 / 6363) ≤ (108672763 / 500000000) := by
  have h := checkLog_sound (w := (1243 / 11483)) (n := 12)
    (lo := (8693821 / 40000000)) (hi := (108672763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6363 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6363 / 5120) = 1/(5120 / 6363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8693821 / 40000000) (108672763 / 500000000) (Real.log (6363 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6363 / 5120) = -Real.log (5120 / 6363) := by
    rw [show ((6363 / 5120) : ℝ) = ((5120 / 6363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (13904639 / 50000000) ≤ -Real.log (3877 / 5120) ∧
    -Real.log (3877 / 5120) ≤ (278092781 / 1000000000) := by
  have h := checkLog_sound (w := (1243 / 8997)) (n := 12)
    (lo := (13904639 / 50000000)) (hi := (278092781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3877) = 1/(3877 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-278092781 / 1000000000) (-13904639 / 50000000) (Real.log (3877 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (198088659 / 500000000) ≤ -Real.log (5120 / 7609) ∧
    -Real.log (5120 / 7609) ≤ (396177319 / 1000000000) := by
  have h := checkLog_sound (w := (2489 / 12729)) (n := 12)
    (lo := (198088659 / 500000000)) (hi := (396177319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7609 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7609 / 5120) = 1/(5120 / 7609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (198088659 / 500000000) (396177319 / 1000000000) (Real.log (7609 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7609 / 5120) = -Real.log (5120 / 7609) := by
    rw [show ((7609 / 5120) : ℝ) = ((5120 / 7609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (166447609 / 250000000) ≤ -Real.log (2631 / 5120) ∧
    -Real.log (2631 / 5120) ≤ (665790437 / 1000000000) := by
  have h := checkLog_sound (w := (2489 / 7751)) (n := 12)
    (lo := (166447609 / 250000000)) (hi := (665790437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2631) = 1/(2631 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-665790437 / 1000000000) (-166447609 / 250000000) (Real.log (2631 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (39578297 / 100000000) ≤ -Real.log (2560 / 3803) ∧
    -Real.log (2560 / 3803) ≤ (395782971 / 1000000000) := by
  have h := checkLog_sound (w := (1243 / 6363)) (n := 12)
    (lo := (39578297 / 100000000)) (hi := (395782971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3803 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3803 / 2560) = 1/(2560 / 3803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (39578297 / 100000000) (395782971 / 1000000000) (Real.log (3803 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3803 / 2560) = -Real.log (2560 / 3803) := by
    rw [show ((3803 / 2560) : ℝ) = ((2560 / 3803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (132930167 / 200000000) ≤ -Real.log (1317 / 2560) ∧
    -Real.log (1317 / 2560) ≤ (166162709 / 250000000) := by
  have h := checkLog_sound (w := (1243 / 3877)) (n := 12)
    (lo := (132930167 / 200000000)) (hi := (166162709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1317) = 1/(1317 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-166162709 / 250000000) (-132930167 / 200000000) (Real.log (1317 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18621391 / 62500000) ≤ -Real.log (250000 / 336771) ∧
    -Real.log (250000 / 336771) ≤ (297942257 / 1000000000) := by
  have h := checkLog_sound (w := (86771 / 586771)) (n := 12)
    (lo := (18621391 / 62500000)) (hi := (297942257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336771 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336771 / 250000) = 1/(250000 / 336771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18621391 / 62500000) (297942257 / 1000000000) (Real.log (336771 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (336771 / 250000) = -Real.log (250000 / 336771) := by
    rw [show ((336771 / 250000) : ℝ) = ((250000 / 336771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (85261359 / 200000000) ≤ -Real.log (163229 / 250000) ∧
    -Real.log (163229 / 250000) ≤ (106576699 / 250000000) := by
  have h := checkLog_sound (w := (86771 / 413229)) (n := 12)
    (lo := (85261359 / 200000000)) (hi := (106576699 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 163229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 163229) = 1/(163229 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-106576699 / 250000000) (-85261359 / 200000000) (Real.log (163229 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (298261413 / 1000000000) ≤ -Real.log (500000 / 673757) ∧
    -Real.log (500000 / 673757) ≤ (149130707 / 500000000) := by
  have h := checkLog_sound (w := (173757 / 1173757)) (n := 12)
    (lo := (298261413 / 1000000000)) (hi := (149130707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673757 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673757 / 500000) = 1/(500000 / 673757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (298261413 / 1000000000) (149130707 / 500000000) (Real.log (673757 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (673757 / 500000) = -Real.log (500000 / 673757) := by
    rw [show ((673757 / 500000) : ℝ) = ((500000 / 673757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (85393119 / 200000000) ≤ -Real.log (326243 / 500000) ∧
    -Real.log (326243 / 500000) ≤ (106741399 / 250000000) := by
  have h := checkLog_sound (w := (173757 / 826243)) (n := 12)
    (lo := (85393119 / 200000000)) (hi := (106741399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 326243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 326243) = 1/(326243 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-106741399 / 250000000) (-85393119 / 200000000) (Real.log (326243 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (226249921 / 1000000000) ≤ -Real.log (1000000 / 1253889) ∧
    -Real.log (1000000 / 1253889) ≤ (113124961 / 500000000) := by
  have h := checkLog_sound (w := (253889 / 2253889)) (n := 12)
    (lo := (226249921 / 1000000000)) (hi := (113124961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1253889 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1253889 / 1000000) = 1/(1000000 / 1253889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (226249921 / 1000000000) (113124961 / 500000000) (Real.log (1253889 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1253889 / 1000000) = -Real.log (1000000 / 1253889) := by
    rw [show ((1253889 / 1000000) : ℝ) = ((1000000 / 1253889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (572033 / 1953125) ≤ -Real.log (746111 / 1000000) ∧
    -Real.log (746111 / 1000000) ≤ (292880897 / 1000000000) := by
  have h := checkLog_sound (w := (253889 / 1746111)) (n := 12)
    (lo := (572033 / 1953125)) (hi := (292880897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 746111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 746111) = 1/(746111 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-292880897 / 1000000000) (-572033 / 1953125) (Real.log (746111 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (226517851 / 1000000000) ≤ -Real.log (40000 / 50169) ∧
    -Real.log (40000 / 50169) ≤ (56629463 / 250000000) := by
  have h := checkLog_sound (w := (10169 / 90169)) (n := 12)
    (lo := (226517851 / 1000000000)) (hi := (56629463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50169 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50169 / 40000) = 1/(40000 / 50169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (226517851 / 1000000000) (56629463 / 250000000) (Real.log (50169 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (50169 / 40000) = -Real.log (40000 / 50169) := by
    rw [show ((50169 / 40000) : ℝ) = ((40000 / 50169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (73332833 / 250000000) ≤ -Real.log (29831 / 40000) ∧
    -Real.log (29831 / 40000) ≤ (293331333 / 1000000000) := by
  have h := checkLog_sound (w := (10169 / 69831)) (n := 12)
    (lo := (73332833 / 250000000)) (hi := (293331333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 29831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 29831) = 1/(29831 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-293331333 / 1000000000) (-73332833 / 250000000) (Real.log (29831 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (14484981 / 20000000) ≤ -Real.log (7812500000 / 16118602929) ∧
    -Real.log (7812500000 / 16118602929) ≤ (181062263 / 250000000) := by
  have h := checkLog_sound (w := (493602929 / 31743602929)) (n := 12)
    (lo := (3110187 / 100000000)) (hi := (31101871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16118602929 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16118602929 / 15625000000) = 1/(7812500000 / 16118602929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14484981 / 20000000) (181062263 / 250000000) (Real.log (16118602929 / 7812500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (16118602929 / 7812500000) = -Real.log (7812500000 / 16118602929) := by
    rw [show ((16118602929 / 7812500000) : ℝ) = ((7812500000 / 16118602929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1416459 / 1953125) ≤ -Real.log (500000000000 / 1032599933179) ∧
    -Real.log (500000000000 / 1032599933179) ≤ (72522701 / 100000000) := by
  have h := checkLog_sound (w := (32599933179 / 2032599933179)) (n := 12)
    (lo := (8019957 / 250000000)) (hi := (32079829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1032599933179 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1032599933179 / 1000000000000) = 1/(500000000000 / 1032599933179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1416459 / 1953125) (72522701 / 100000000) (Real.log (1032599933179 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1032599933179 / 500000000000) = -Real.log (500000000000 / 1032599933179) := by
    rw [show ((1032599933179 / 500000000000) : ℝ) = ((500000000000 / 1032599933179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (519130817 / 1000000000) ≤ -Real.log (500000000000 / 840283148217) ∧
    -Real.log (500000000000 / 840283148217) ≤ (259565409 / 500000000) := by
  have h := checkLog_sound (w := (340283148217 / 1340283148217)) (n := 12)
    (lo := (519130817 / 1000000000)) (hi := (259565409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((840283148217 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(840283148217 / 500000000000) = 1/(500000000000 / 840283148217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (519130817 / 1000000000) (259565409 / 500000000) (Real.log (840283148217 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (840283148217 / 500000000000) = -Real.log (500000000000 / 840283148217) := by
    rw [show ((840283148217 / 500000000000) : ℝ) = ((500000000000 / 840283148217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (16245287 / 31250000) ≤ -Real.log (500000000000 / 840886996749) ∧
    -Real.log (500000000000 / 840886996749) ≤ (103969837 / 200000000) := by
  have h := checkLog_sound (w := (340886996749 / 1340886996749)) (n := 12)
    (lo := (16245287 / 31250000)) (hi := (103969837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((840886996749 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(840886996749 / 500000000000) = 1/(500000000000 / 840886996749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (16245287 / 31250000) (103969837 / 200000000) (Real.log (840886996749 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (840886996749 / 500000000000) = -Real.log (500000000000 / 840886996749) := by
    rw [show ((840886996749 / 500000000000) : ℝ) = ((500000000000 / 840886996749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0327
