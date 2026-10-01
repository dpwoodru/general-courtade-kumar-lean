import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0166
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

theorem reflection_log_1_neg : (140411331 / 500000000) ≤ -Real.log (256 / 339) ∧
    -Real.log (256 / 339) ≤ (280822663 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 595)) (n := 12)
    (lo := (140411331 / 500000000)) (hi := (280822663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339 / 256) = 1/(256 / 339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (140411331 / 500000000) (280822663 / 1000000000) (Real.log (339 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (339 / 256) = -Real.log (256 / 339) := by
    rw [show ((339 / 256) : ℝ) = ((256 / 339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (391885849 / 1000000000) ≤ -Real.log (173 / 256) ∧
    -Real.log (173 / 256) ≤ (7837717 / 20000000) := by
  have h := checkLog_sound (w := (83 / 429)) (n := 12)
    (lo := (391885849 / 1000000000)) (hi := (7837717 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 173) = 1/(173 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-7837717 / 20000000) (-391885849 / 1000000000) (Real.log (173 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (280380087 / 1000000000) ≤ -Real.log (5120 / 6777) ∧
    -Real.log (5120 / 6777) ≤ (35047511 / 125000000) := by
  have h := checkLog_sound (w := (1657 / 11897)) (n := 12)
    (lo := (280380087 / 1000000000)) (hi := (35047511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6777 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6777 / 5120) = 1/(5120 / 6777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (280380087 / 1000000000) (35047511 / 125000000) (Real.log (6777 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6777 / 5120) = -Real.log (5120 / 6777) := by
    rw [show ((6777 / 5120) : ℝ) = ((5120 / 6777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (391019173 / 1000000000) ≤ -Real.log (3463 / 5120) ∧
    -Real.log (3463 / 5120) ≤ (195509587 / 500000000) := by
  have h := checkLog_sound (w := (1657 / 8583)) (n := 12)
    (lo := (391019173 / 1000000000)) (hi := (195509587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3463) = 1/(3463 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-195509587 / 500000000) (-391019173 / 1000000000) (Real.log (3463 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (499827869 / 1000000000) ≤ -Real.log (128 / 211) ∧
    -Real.log (128 / 211) ≤ (49982787 / 100000000) := by
  have h := checkLog_sound (w := (83 / 339)) (n := 12)
    (lo := (499827869 / 1000000000)) (hi := (49982787 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211 / 128) = 1/(128 / 211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (499827869 / 1000000000) (49982787 / 100000000) (Real.log (211 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (211 / 128) = -Real.log (128 / 211) := by
    rw [show ((211 / 128) : ℝ) = ((128 / 211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1045367773 / 1000000000) ≤ -Real.log (45 / 128) ∧
    -Real.log (45 / 128) ≤ (41814711 / 40000000) := by
  have h := checkLog_sound (w := (19 / 109)) (n := 12)
    (lo := (352220593 / 1000000000)) (hi := (176110297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 45) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 45) = 1/(45 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-41814711 / 40000000) (-1045367773 / 1000000000) (Real.log (45 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (124779179 / 250000000) ≤ -Real.log (2560 / 4217) ∧
    -Real.log (2560 / 4217) ≤ (499116717 / 1000000000) := by
  have h := checkLog_sound (w := (1657 / 6777)) (n := 12)
    (lo := (124779179 / 250000000)) (hi := (499116717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4217 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4217 / 2560) = 1/(2560 / 4217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (124779179 / 250000000) (499116717 / 1000000000) (Real.log (4217 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4217 / 2560) = -Real.log (2560 / 4217) := by
    rw [show ((4217 / 2560) : ℝ) = ((2560 / 4217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1042039983 / 1000000000) ≤ -Real.log (903 / 2560) ∧
    -Real.log (903 / 2560) ≤ (208407997 / 200000000) := by
  have h := checkLog_sound (w := (377 / 2183)) (n := 12)
    (lo := (348892803 / 1000000000)) (hi := (87223201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 903) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 903) = 1/(903 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-208407997 / 200000000) (-1042039983 / 1000000000) (Real.log (903 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (383559591 / 1000000000) ≤ -Real.log (1000000 / 1467499) ∧
    -Real.log (1000000 / 1467499) ≤ (47944949 / 125000000) := by
  have h := checkLog_sound (w := (467499 / 2467499)) (n := 12)
    (lo := (383559591 / 1000000000)) (hi := (47944949 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1467499 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1467499 / 1000000) = 1/(1000000 / 1467499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (383559591 / 1000000000) (47944949 / 125000000) (Real.log (1467499 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1467499 / 1000000) = -Real.log (1000000 / 1467499) := by
    rw [show ((1467499 / 1000000) : ℝ) = ((1000000 / 1467499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (630170503 / 1000000000) ≤ -Real.log (532501 / 1000000) ∧
    -Real.log (532501 / 1000000) ≤ (78771313 / 125000000) := by
  have h := checkLog_sound (w := (467499 / 1532501)) (n := 12)
    (lo := (630170503 / 1000000000)) (hi := (78771313 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 532501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 532501) = 1/(532501 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-78771313 / 125000000) (-630170503 / 1000000000) (Real.log (532501 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (384167243 / 1000000000) ≤ -Real.log (1000000 / 1468391) ∧
    -Real.log (1000000 / 1468391) ≤ (96041811 / 250000000) := by
  have h := checkLog_sound (w := (468391 / 2468391)) (n := 12)
    (lo := (384167243 / 1000000000)) (hi := (96041811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1468391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1468391 / 1000000) = 1/(1000000 / 1468391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (384167243 / 1000000000) (96041811 / 250000000) (Real.log (1468391 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1468391 / 1000000) = -Real.log (1000000 / 1468391) := by
    rw [show ((1468391 / 1000000) : ℝ) = ((1000000 / 1468391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (315923511 / 500000000) ≤ -Real.log (531609 / 1000000) ∧
    -Real.log (531609 / 1000000) ≤ (631847023 / 1000000000) := by
  have h := checkLog_sound (w := (468391 / 1531609)) (n := 12)
    (lo := (315923511 / 500000000)) (hi := (631847023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 531609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 531609) = 1/(531609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-631847023 / 1000000000) (-315923511 / 500000000) (Real.log (531609 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (150717039 / 500000000) ≤ -Real.log (250000 / 337949) ∧
    -Real.log (250000 / 337949) ≤ (301434079 / 1000000000) := by
  have h := checkLog_sound (w := (87949 / 587949)) (n := 12)
    (lo := (150717039 / 500000000)) (hi := (301434079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337949 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(337949 / 250000) = 1/(250000 / 337949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (150717039 / 500000000) (301434079 / 1000000000) (Real.log (337949 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (337949 / 250000) = -Real.log (250000 / 337949) := by
    rw [show ((337949 / 250000) : ℝ) = ((250000 / 337949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (433549817 / 1000000000) ≤ -Real.log (162051 / 250000) ∧
    -Real.log (162051 / 250000) ≤ (216774909 / 500000000) := by
  have h := checkLog_sound (w := (87949 / 412051)) (n := 12)
    (lo := (433549817 / 1000000000)) (hi := (216774909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 162051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 162051) = 1/(162051 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-216774909 / 500000000) (-433549817 / 1000000000) (Real.log (162051 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (301993917 / 1000000000) ≤ -Real.log (1000000 / 1352553) ∧
    -Real.log (1000000 / 1352553) ≤ (150996959 / 500000000) := by
  have h := checkLog_sound (w := (352553 / 2352553)) (n := 12)
    (lo := (301993917 / 1000000000)) (hi := (150996959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1352553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1352553 / 1000000) = 1/(1000000 / 1352553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (301993917 / 1000000000) (150996959 / 500000000) (Real.log (1352553 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1352553 / 1000000) = -Real.log (1000000 / 1352553) := by
    rw [show ((1352553 / 1000000) : ℝ) = ((1000000 / 1352553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (217359171 / 500000000) ≤ -Real.log (647447 / 1000000) ∧
    -Real.log (647447 / 1000000) ≤ (434718343 / 1000000000) := by
  have h := checkLog_sound (w := (352553 / 1647447)) (n := 12)
    (lo := (217359171 / 500000000)) (hi := (434718343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 647447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 647447) = 1/(647447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-434718343 / 1000000000) (-217359171 / 500000000) (Real.log (647447 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (506865047 / 500000000) ≤ -Real.log (500000000000 / 1377930745669) ∧
    -Real.log (500000000000 / 1377930745669) ≤ (63358131 / 62500000) := by
  have h := checkLog_sound (w := (377930745669 / 2377930745669)) (n := 12)
    (lo := (160291457 / 500000000)) (hi := (64116583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1377930745669 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1377930745669 / 1000000000000) = 1/(500000000000 / 1377930745669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (506865047 / 500000000) (63358131 / 62500000) (Real.log (1377930745669 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1377930745669 / 500000000000) = -Real.log (500000000000 / 1377930745669) := by
    rw [show ((1377930745669 / 500000000000) : ℝ) = ((500000000000 / 1377930745669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (203202853 / 200000000) ≤ -Real.log (250000000000 / 690540886253) ∧
    -Real.log (250000000000 / 690540886253) ≤ (1016014267 / 1000000000) := by
  have h := checkLog_sound (w := (190540886253 / 1190540886253)) (n := 12)
    (lo := (64573417 / 200000000)) (hi := (161433543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690540886253 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(690540886253 / 500000000000) = 1/(250000000000 / 690540886253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (203202853 / 200000000) (1016014267 / 1000000000) (Real.log (690540886253 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (690540886253 / 250000000000) = -Real.log (250000000000 / 690540886253) := by
    rw [show ((690540886253 / 250000000000) : ℝ) = ((250000000000 / 690540886253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (146996779 / 200000000) ≤ -Real.log (125000000000 / 260681051027) ∧
    -Real.log (125000000000 / 260681051027) ≤ (734983897 / 1000000000) := by
  have h := checkLog_sound (w := (10681051027 / 510681051027)) (n := 12)
    (lo := (8367343 / 200000000)) (hi := (10459179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((260681051027 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(260681051027 / 250000000000) = 1/(125000000000 / 260681051027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (146996779 / 200000000) (734983897 / 1000000000) (Real.log (260681051027 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (260681051027 / 125000000000) = -Real.log (125000000000 / 260681051027) := by
    rw [show ((260681051027 / 125000000000) : ℝ) = ((125000000000 / 260681051027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (736712259 / 1000000000) ≤ -Real.log (100000000000 / 208905593817) ∧
    -Real.log (100000000000 / 208905593817) ≤ (736712261 / 1000000000) := by
  have h := checkLog_sound (w := (8905593817 / 408905593817)) (n := 12)
    (lo := (43565079 / 1000000000)) (hi := (1089127 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((208905593817 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(208905593817 / 200000000000) = 1/(100000000000 / 208905593817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (736712259 / 1000000000) (736712261 / 1000000000) (Real.log (208905593817 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (208905593817 / 100000000000) = -Real.log (100000000000 / 208905593817) := by
    rw [show ((208905593817 / 100000000000) : ℝ) = ((100000000000 / 208905593817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0166
