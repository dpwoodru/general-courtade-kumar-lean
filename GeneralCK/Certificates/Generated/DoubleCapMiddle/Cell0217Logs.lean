import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0217
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

theorem reflection_log_1_neg : (128998887 / 500000000) ≤ -Real.log (5120 / 6627) ∧
    -Real.log (5120 / 6627) ≤ (10319911 / 40000000) := by
  have h := checkLog_sound (w := (1507 / 11747)) (n := 12)
    (lo := (128998887 / 500000000)) (hi := (10319911 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6627 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6627 / 5120) = 1/(5120 / 6627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128998887 / 500000000) (10319911 / 40000000) (Real.log (6627 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6627 / 5120) = -Real.log (5120 / 6627) := by
    rw [show ((6627 / 5120) : ℝ) = ((5120 / 6627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (174307993 / 500000000) ≤ -Real.log (3613 / 5120) ∧
    -Real.log (3613 / 5120) ≤ (348615987 / 1000000000) := by
  have h := checkLog_sound (w := (1507 / 8733)) (n := 12)
    (lo := (174307993 / 500000000)) (hi := (348615987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3613) = 1/(3613 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-348615987 / 1000000000) (-174307993 / 500000000) (Real.log (3613 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128772489 / 500000000) ≤ -Real.log (160 / 207) ∧
    -Real.log (160 / 207) ≤ (257544979 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 367)) (n := 12)
    (lo := (128772489 / 500000000)) (hi := (257544979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(207 / 160) = 1/(160 / 207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128772489 / 500000000) (257544979 / 1000000000) (Real.log (207 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (207 / 160) = -Real.log (160 / 207) := by
    rw [show ((207 / 160) : ℝ) = ((160 / 207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (86946499 / 250000000) ≤ -Real.log (113 / 160) ∧
    -Real.log (113 / 160) ≤ (347785997 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 273)) (n := 12)
    (lo := (86946499 / 250000000)) (hi := (347785997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 113) = 1/(113 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-347785997 / 1000000000) (-86946499 / 250000000) (Real.log (113 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (7232787 / 15625000) ≤ -Real.log (2560 / 4067) ∧
    -Real.log (2560 / 4067) ≤ (462898369 / 1000000000) := by
  have h := checkLog_sound (w := (1507 / 6627)) (n := 12)
    (lo := (7232787 / 15625000)) (hi := (462898369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4067 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4067 / 2560) = 1/(2560 / 4067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (7232787 / 15625000) (462898369 / 1000000000) (Real.log (4067 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4067 / 2560) = -Real.log (2560 / 4067) := by
    rw [show ((4067 / 2560) : ℝ) = ((2560 / 4067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (111045503 / 125000000) ≤ -Real.log (1053 / 2560) ∧
    -Real.log (1053 / 2560) ≤ (444182013 / 500000000) := by
  have h := checkLog_sound (w := (227 / 2333)) (n := 12)
    (lo := (48804211 / 250000000)) (hi := (39043369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1053) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1053) = 1/(1053 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-444182013 / 500000000) (-111045503 / 125000000) (Real.log (1053 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (462160451 / 1000000000) ≤ -Real.log (80 / 127) ∧
    -Real.log (80 / 127) ≤ (115540113 / 250000000) := by
  have h := checkLog_sound (w := (47 / 207)) (n := 12)
    (lo := (462160451 / 1000000000)) (hi := (115540113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127 / 80) = 1/(80 / 127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (462160451 / 1000000000) (115540113 / 250000000) (Real.log (127 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (127 / 80) = -Real.log (80 / 127) := by
    rw [show ((127 / 80) : ℝ) = ((80 / 127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (27672471 / 31250000) ≤ -Real.log (33 / 80) ∧
    -Real.log (33 / 80) ≤ (442759537 / 500000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 33) = 1/(33 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-442759537 / 500000000) (-27672471 / 31250000) (Real.log (33 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (352387767 / 1000000000) ≤ -Real.log (50000 / 71123) ∧
    -Real.log (50000 / 71123) ≤ (44048471 / 125000000) := by
  have h := checkLog_sound (w := (21123 / 121123)) (n := 12)
    (lo := (352387767 / 1000000000)) (hi := (44048471 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71123 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71123 / 50000) = 1/(50000 / 71123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (352387767 / 1000000000) (44048471 / 125000000) (Real.log (71123 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (71123 / 50000) = -Real.log (50000 / 71123) := by
    rw [show ((71123 / 50000) : ℝ) = ((50000 / 71123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (274488787 / 500000000) ≤ -Real.log (28877 / 50000) ∧
    -Real.log (28877 / 50000) ≤ (21959103 / 40000000) := by
  have h := checkLog_sound (w := (21123 / 78877)) (n := 12)
    (lo := (274488787 / 500000000)) (hi := (21959103 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 28877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 28877) = 1/(28877 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-21959103 / 40000000) (-274488787 / 500000000) (Real.log (28877 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (176502057 / 500000000) ≤ -Real.log (1000000 / 1423337) ∧
    -Real.log (1000000 / 1423337) ≤ (70600823 / 200000000) := by
  have h := checkLog_sound (w := (423337 / 2423337)) (n := 12)
    (lo := (176502057 / 500000000)) (hi := (70600823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1423337 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1423337 / 1000000) = 1/(1000000 / 1423337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (176502057 / 500000000) (70600823 / 200000000) (Real.log (1423337 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1423337 / 1000000) = -Real.log (1000000 / 1423337) := by
    rw [show ((1423337 / 1000000) : ℝ) = ((1000000 / 1423337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (275248619 / 500000000) ≤ -Real.log (576663 / 1000000) ∧
    -Real.log (576663 / 1000000) ≤ (550497239 / 1000000000) := by
  have h := checkLog_sound (w := (423337 / 1576663)) (n := 12)
    (lo := (275248619 / 500000000)) (hi := (550497239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 576663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 576663) = 1/(576663 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-550497239 / 1000000000) (-275248619 / 500000000) (Real.log (576663 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (136622047 / 500000000) ≤ -Real.log (1000000 / 1314221) ∧
    -Real.log (1000000 / 1314221) ≤ (54648819 / 200000000) := by
  have h := checkLog_sound (w := (314221 / 2314221)) (n := 12)
    (lo := (136622047 / 500000000)) (hi := (54648819 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1314221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1314221 / 1000000) = 1/(1000000 / 1314221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (136622047 / 500000000) (54648819 / 200000000) (Real.log (1314221 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1314221 / 1000000) = -Real.log (1000000 / 1314221) := by
    rw [show ((1314221 / 1000000) : ℝ) = ((1000000 / 1314221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (18859993 / 50000000) ≤ -Real.log (685779 / 1000000) ∧
    -Real.log (685779 / 1000000) ≤ (377199861 / 1000000000) := by
  have h := checkLog_sound (w := (314221 / 1685779)) (n := 12)
    (lo := (18859993 / 50000000)) (hi := (377199861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 685779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 685779) = 1/(685779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-377199861 / 1000000000) (-18859993 / 50000000) (Real.log (685779 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (273791797 / 1000000000) ≤ -Real.log (1000000 / 1314941) ∧
    -Real.log (1000000 / 1314941) ≤ (136895899 / 500000000) := by
  have h := checkLog_sound (w := (314941 / 2314941)) (n := 12)
    (lo := (273791797 / 1000000000)) (hi := (136895899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1314941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1314941 / 1000000) = 1/(1000000 / 1314941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (273791797 / 1000000000) (136895899 / 500000000) (Real.log (1314941 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1314941 / 1000000) = -Real.log (1000000 / 1314941) := by
    rw [show ((1314941 / 1000000) : ℝ) = ((1000000 / 1314941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (378250313 / 1000000000) ≤ -Real.log (685059 / 1000000) ∧
    -Real.log (685059 / 1000000) ≤ (189125157 / 500000000) := by
  have h := checkLog_sound (w := (314941 / 1685059)) (n := 12)
    (lo := (378250313 / 1000000000)) (hi := (189125157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 685059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 685059) = 1/(685059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-189125157 / 500000000) (-378250313 / 1000000000) (Real.log (685059 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (901365341 / 1000000000) ≤ -Real.log (250000000000 / 615740901063) ∧
    -Real.log (250000000000 / 615740901063) ≤ (901365343 / 1000000000) := by
  have h := checkLog_sound (w := (115740901063 / 1115740901063)) (n := 12)
    (lo := (208218161 / 1000000000)) (hi := (104109081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615740901063 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(615740901063 / 500000000000) = 1/(250000000000 / 615740901063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (901365341 / 1000000000) (901365343 / 1000000000) (Real.log (615740901063 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (615740901063 / 250000000000) = -Real.log (250000000000 / 615740901063) := by
    rw [show ((615740901063 / 250000000000) : ℝ) = ((250000000000 / 615740901063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (112937669 / 125000000) ≤ -Real.log (62500000000 / 154264384051) ∧
    -Real.log (62500000000 / 154264384051) ≤ (451750677 / 500000000) := by
  have h := checkLog_sound (w := (29264384051 / 279264384051)) (n := 12)
    (lo := (52588543 / 250000000)) (hi := (210354173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154264384051 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(154264384051 / 125000000000) = 1/(62500000000 / 154264384051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (112937669 / 125000000) (451750677 / 500000000) (Real.log (154264384051 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (154264384051 / 62500000000) = -Real.log (62500000000 / 154264384051) := by
    rw [show ((154264384051 / 62500000000) : ℝ) = ((62500000000 / 154264384051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (130088791 / 200000000) ≤ -Real.log (31250000000 / 59887232257) ∧
    -Real.log (31250000000 / 59887232257) ≤ (162610989 / 250000000) := by
  have h := checkLog_sound (w := (28637232257 / 91137232257)) (n := 12)
    (lo := (130088791 / 200000000)) (hi := (162610989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59887232257 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59887232257 / 31250000000) = 1/(31250000000 / 59887232257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (130088791 / 200000000) (162610989 / 250000000) (Real.log (59887232257 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (59887232257 / 31250000000) = -Real.log (31250000000 / 59887232257) := by
    rw [show ((59887232257 / 31250000000) : ℝ) = ((31250000000 / 59887232257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (65204211 / 100000000) ≤ -Real.log (500000000000 / 959728286177) ∧
    -Real.log (500000000000 / 959728286177) ≤ (652042111 / 1000000000) := by
  have h := checkLog_sound (w := (459728286177 / 1459728286177)) (n := 12)
    (lo := (65204211 / 100000000)) (hi := (652042111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959728286177 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959728286177 / 500000000000) = 1/(500000000000 / 959728286177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (65204211 / 100000000) (652042111 / 1000000000) (Real.log (959728286177 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (959728286177 / 500000000000) = -Real.log (500000000000 / 959728286177) := by
    rw [show ((959728286177 / 500000000000) : ℝ) = ((500000000000 / 959728286177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0217
