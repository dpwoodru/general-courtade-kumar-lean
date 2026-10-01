import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0169
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

theorem reflection_log_1_neg : (279494347 / 1000000000) ≤ -Real.log (5120 / 6771) ∧
    -Real.log (5120 / 6771) ≤ (69873587 / 250000000) := by
  have h := checkLog_sound (w := (1651 / 11891)) (n := 12)
    (lo := (279494347 / 1000000000)) (hi := (69873587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6771 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6771 / 5120) = 1/(5120 / 6771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (279494347 / 1000000000) (69873587 / 250000000) (Real.log (6771 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6771 / 5120) = -Real.log (5120 / 6771) := by
    rw [show ((6771 / 5120) : ℝ) = ((5120 / 6771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (389288071 / 1000000000) ≤ -Real.log (3469 / 5120) ∧
    -Real.log (3469 / 5120) ≤ (48661009 / 125000000) := by
  have h := checkLog_sound (w := (1651 / 8589)) (n := 12)
    (lo := (389288071 / 1000000000)) (hi := (48661009 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3469) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3469) = 1/(3469 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-48661009 / 125000000) (-389288071 / 1000000000) (Real.log (3469 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (279051183 / 1000000000) ≤ -Real.log (320 / 423) ∧
    -Real.log (320 / 423) ≤ (17440699 / 62500000) := by
  have h := checkLog_sound (w := (103 / 743)) (n := 12)
    (lo := (279051183 / 1000000000)) (hi := (17440699 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((423 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(423 / 320) = 1/(320 / 423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (279051183 / 1000000000) (17440699 / 62500000) (Real.log (423 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (423 / 320) = -Real.log (320 / 423) := by
    rw [show ((423 / 320) : ℝ) = ((320 / 423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (194211821 / 500000000) ≤ -Real.log (217 / 320) ∧
    -Real.log (217 / 320) ≤ (388423643 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 537)) (n := 12)
    (lo := (194211821 / 500000000)) (hi := (388423643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 217) = 1/(217 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-388423643 / 1000000000) (-194211821 / 500000000) (Real.log (217 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (49769289 / 100000000) ≤ -Real.log (2560 / 4211) ∧
    -Real.log (2560 / 4211) ≤ (497692891 / 1000000000) := by
  have h := checkLog_sound (w := (1651 / 6771)) (n := 12)
    (lo := (49769289 / 100000000)) (hi := (497692891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4211 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4211 / 2560) = 1/(2560 / 4211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (49769289 / 100000000) (497692891 / 1000000000) (Real.log (4211 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4211 / 2560) = -Real.log (2560 / 4211) := by
    rw [show ((4211 / 2560) : ℝ) = ((2560 / 4211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (517708721 / 500000000) ≤ -Real.log (909 / 2560) ∧
    -Real.log (909 / 2560) ≤ (258854361 / 250000000) := by
  have h := checkLog_sound (w := (371 / 2189)) (n := 12)
    (lo := (171135131 / 500000000)) (hi := (342270263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 909) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 909) = 1/(909 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-258854361 / 250000000) (-517708721 / 500000000) (Real.log (909 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (62122527 / 125000000) ≤ -Real.log (160 / 263) ∧
    -Real.log (160 / 263) ≤ (496980217 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 423)) (n := 12)
    (lo := (62122527 / 125000000)) (hi := (496980217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(263 / 160) = 1/(160 / 263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (62122527 / 125000000) (496980217 / 1000000000) (Real.log (263 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (263 / 160) = -Real.log (160 / 263) := by
    rw [show ((263 / 160) : ℝ) = ((160 / 263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (516061273 / 500000000) ≤ -Real.log (57 / 160) ∧
    -Real.log (57 / 160) ≤ (258030637 / 250000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 57) = 1/(57 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-258030637 / 250000000) (-516061273 / 500000000) (Real.log (57 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (381737829 / 1000000000) ≤ -Real.log (250000 / 366207) ∧
    -Real.log (250000 / 366207) ≤ (38173783 / 100000000) := by
  have h := checkLog_sound (w := (116207 / 616207)) (n := 12)
    (lo := (381737829 / 1000000000)) (hi := (38173783 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((366207 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(366207 / 250000) = 1/(250000 / 366207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (381737829 / 1000000000) (38173783 / 100000000) (Real.log (366207 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (366207 / 250000) = -Real.log (250000 / 366207) := by
    rw [show ((366207 / 250000) : ℝ) = ((250000 / 366207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (39072943 / 62500000) ≤ -Real.log (133793 / 250000) ∧
    -Real.log (133793 / 250000) ≤ (625167089 / 1000000000) := by
  have h := checkLog_sound (w := (116207 / 383793)) (n := 12)
    (lo := (39072943 / 62500000)) (hi := (625167089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 133793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 133793) = 1/(133793 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-625167089 / 1000000000) (-39072943 / 62500000) (Real.log (133793 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (382345907 / 1000000000) ≤ -Real.log (1000000 / 1465719) ∧
    -Real.log (1000000 / 1465719) ≤ (95586477 / 250000000) := by
  have h := checkLog_sound (w := (465719 / 2465719)) (n := 12)
    (lo := (382345907 / 1000000000)) (hi := (95586477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1465719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1465719 / 1000000) = 1/(1000000 / 1465719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (382345907 / 1000000000) (95586477 / 250000000) (Real.log (1465719 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1465719 / 1000000) = -Real.log (1000000 / 1465719) := by
    rw [show ((1465719 / 1000000) : ℝ) = ((1000000 / 1465719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (626833361 / 1000000000) ≤ -Real.log (534281 / 1000000) ∧
    -Real.log (534281 / 1000000) ≤ (313416681 / 500000000) := by
  have h := checkLog_sound (w := (465719 / 1534281)) (n := 12)
    (lo := (626833361 / 1000000000)) (hi := (313416681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 534281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 534281) = 1/(534281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-313416681 / 500000000) (-626833361 / 1000000000) (Real.log (534281 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (59951573 / 200000000) ≤ -Real.log (250000 / 337383) ∧
    -Real.log (250000 / 337383) ≤ (149878933 / 500000000) := by
  have h := checkLog_sound (w := (87383 / 587383)) (n := 12)
    (lo := (59951573 / 200000000)) (hi := (149878933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337383 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(337383 / 250000) = 1/(250000 / 337383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (59951573 / 200000000) (149878933 / 500000000) (Real.log (337383 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (337383 / 250000) = -Real.log (250000 / 337383) := by
    rw [show ((337383 / 250000) : ℝ) = ((250000 / 337383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (17202527 / 40000000) ≤ -Real.log (162617 / 250000) ∧
    -Real.log (162617 / 250000) ≤ (53757897 / 125000000) := by
  have h := checkLog_sound (w := (87383 / 412617)) (n := 12)
    (lo := (17202527 / 40000000)) (hi := (53757897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 162617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 162617) = 1/(162617 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-53757897 / 125000000) (-17202527 / 40000000) (Real.log (162617 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (150158581 / 500000000) ≤ -Real.log (1000000 / 1350287) ∧
    -Real.log (1000000 / 1350287) ≤ (300317163 / 1000000000) := by
  have h := checkLog_sound (w := (350287 / 2350287)) (n := 12)
    (lo := (150158581 / 500000000)) (hi := (300317163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1350287 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1350287 / 1000000) = 1/(1000000 / 1350287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (150158581 / 500000000) (300317163 / 1000000000) (Real.log (1350287 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1350287 / 1000000) = -Real.log (1000000 / 1350287) := by
    rw [show ((1350287 / 1000000) : ℝ) = ((1000000 / 1350287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53903069 / 125000000) ≤ -Real.log (649713 / 1000000) ∧
    -Real.log (649713 / 1000000) ≤ (431224553 / 1000000000) := by
  have h := checkLog_sound (w := (350287 / 1649713)) (n := 12)
    (lo := (53903069 / 125000000)) (hi := (431224553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 649713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 649713) = 1/(649713 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-431224553 / 1000000000) (-53903069 / 125000000) (Real.log (649713 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1006904917 / 1000000000) ≤ -Real.log (1953125000 / 5345930257) ∧
    -Real.log (1953125000 / 5345930257) ≤ (1006904919 / 1000000000) := by
  have h := checkLog_sound (w := (1439680257 / 9252180257)) (n := 12)
    (lo := (313757737 / 1000000000)) (hi := (156878869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5345930257 / 3906250000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5345930257 / 3906250000) = 1/(1953125000 / 5345930257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1006904917 / 1000000000) (1006904919 / 1000000000) (Real.log (5345930257 / 1953125000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5345930257 / 1953125000) = -Real.log (1953125000 / 5345930257) := by
    rw [show ((5345930257 / 1953125000) : ℝ) = ((1953125000 / 5345930257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1009179267 / 1000000000) ≤ -Real.log (31250000000 / 85729641799) ∧
    -Real.log (31250000000 / 85729641799) ≤ (1009179269 / 1000000000) := by
  have h := checkLog_sound (w := (23229641799 / 148229641799)) (n := 12)
    (lo := (316032087 / 1000000000)) (hi := (39504011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85729641799 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(85729641799 / 62500000000) = 1/(31250000000 / 85729641799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1009179267 / 1000000000) (1009179269 / 1000000000) (Real.log (85729641799 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (85729641799 / 31250000000) = -Real.log (31250000000 / 85729641799) := by
    rw [show ((85729641799 / 31250000000) : ℝ) = ((31250000000 / 85729641799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9122763 / 12500000) ≤ -Real.log (250000000000 / 518677321559) ∧
    -Real.log (250000000000 / 518677321559) ≤ (364910521 / 500000000) := by
  have h := checkLog_sound (w := (18677321559 / 1018677321559)) (n := 12)
    (lo := (1833693 / 50000000)) (hi := (36673861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((518677321559 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(518677321559 / 500000000000) = 1/(250000000000 / 518677321559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (9122763 / 12500000) (364910521 / 500000000) (Real.log (518677321559 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (518677321559 / 250000000000) = -Real.log (250000000000 / 518677321559) := by
    rw [show ((518677321559 / 250000000000) : ℝ) = ((250000000000 / 518677321559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (731541713 / 1000000000) ≤ -Real.log (125000000000 / 259785282117) ∧
    -Real.log (125000000000 / 259785282117) ≤ (146308343 / 200000000) := by
  have h := checkLog_sound (w := (9785282117 / 509785282117)) (n := 12)
    (lo := (38394533 / 1000000000)) (hi := (19197267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259785282117 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(259785282117 / 250000000000) = 1/(125000000000 / 259785282117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (731541713 / 1000000000) (146308343 / 200000000) (Real.log (259785282117 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (259785282117 / 125000000000) = -Real.log (125000000000 / 259785282117) := by
    rw [show ((259785282117 / 125000000000) : ℝ) = ((125000000000 / 259785282117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0169
