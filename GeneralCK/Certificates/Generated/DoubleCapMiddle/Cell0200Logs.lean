import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0200
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

theorem reflection_log_1_neg : (132832051 / 500000000) ≤ -Real.log (2560 / 3339) ∧
    -Real.log (2560 / 3339) ≤ (265664103 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 5899)) (n := 12)
    (lo := (132832051 / 500000000)) (hi := (265664103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3339 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3339 / 2560) = 1/(2560 / 3339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (132832051 / 500000000) (265664103 / 1000000000) (Real.log (3339 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3339 / 2560) = -Real.log (2560 / 3339) := by
    rw [show ((3339 / 2560) : ℝ) = ((2560 / 3339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (181416127 / 500000000) ≤ -Real.log (1781 / 2560) ∧
    -Real.log (1781 / 2560) ≤ (72566451 / 200000000) := by
  have h := checkLog_sound (w := (779 / 4341)) (n := 12)
    (lo := (181416127 / 500000000)) (hi := (72566451 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1781) = 1/(1781 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-72566451 / 200000000) (-181416127 / 500000000) (Real.log (1781 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (53042953 / 200000000) ≤ -Real.log (1024 / 1335) ∧
    -Real.log (1024 / 1335) ≤ (132607383 / 500000000) := by
  have h := checkLog_sound (w := (311 / 2359)) (n := 12)
    (lo := (53042953 / 200000000)) (hi := (132607383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1335 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1335 / 1024) = 1/(1024 / 1335) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (53042953 / 200000000) (132607383 / 500000000) (Real.log (1335 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1335 / 1024) = -Real.log (1024 / 1335) := by
    rw [show ((1335 / 1024) : ℝ) = ((1024 / 1335) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (72398077 / 200000000) ≤ -Real.log (713 / 1024) ∧
    -Real.log (713 / 1024) ≤ (180995193 / 500000000) := by
  have h := checkLog_sound (w := (311 / 1737)) (n := 12)
    (lo := (72398077 / 200000000)) (hi := (180995193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 713) = 1/(713 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-180995193 / 500000000) (-72398077 / 200000000) (Real.log (713 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (9507207 / 20000000) ≤ -Real.log (1280 / 2059) ∧
    -Real.log (1280 / 2059) ≤ (475360351 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 3339)) (n := 12)
    (lo := (9507207 / 20000000)) (hi := (475360351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2059 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2059 / 1280) = 1/(1280 / 2059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (9507207 / 20000000) (475360351 / 1000000000) (Real.log (2059 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2059 / 1280) = -Real.log (1280 / 2059) := by
    rw [show ((2059 / 1280) : ℝ) = ((1280 / 2059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (187601851 / 200000000) ≤ -Real.log (501 / 1280) ∧
    -Real.log (501 / 1280) ≤ (938009257 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 1141)) (n := 12)
    (lo := (9794483 / 40000000)) (hi := (61215519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 501) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 501) = 1/(501 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-938009257 / 1000000000) (-187601851 / 200000000) (Real.log (501 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (18985263 / 40000000) ≤ -Real.log (512 / 823) ∧
    -Real.log (512 / 823) ≤ (59328947 / 125000000) := by
  have h := checkLog_sound (w := (311 / 1335)) (n := 12)
    (lo := (18985263 / 40000000)) (hi := (59328947 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823 / 512) = 1/(512 / 823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (18985263 / 40000000) (59328947 / 125000000) (Real.log (823 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (823 / 512) = -Real.log (512 / 823) := by
    rw [show ((823 / 512) : ℝ) = ((512 / 823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (233754929 / 250000000) ≤ -Real.log (201 / 512) ∧
    -Real.log (201 / 512) ≤ (467509859 / 500000000) := by
  have h := checkLog_sound (w := (55 / 457)) (n := 12)
    (lo := (30234067 / 125000000)) (hi := (241872537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 201) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 201) = 1/(201 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-467509859 / 500000000) (-233754929 / 250000000) (Real.log (201 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (11338427 / 31250000) ≤ -Real.log (1000000 / 1437391) ∧
    -Real.log (1000000 / 1437391) ≤ (72565933 / 200000000) := by
  have h := checkLog_sound (w := (437391 / 2437391)) (n := 12)
    (lo := (11338427 / 31250000)) (hi := (72565933 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1437391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1437391 / 1000000) = 1/(1000000 / 1437391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (11338427 / 31250000) (72565933 / 200000000) (Real.log (1437391 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1437391 / 1000000) = -Real.log (1000000 / 1437391) := by
    rw [show ((1437391 / 1000000) : ℝ) = ((1000000 / 1437391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (115034077 / 200000000) ≤ -Real.log (562609 / 1000000) ∧
    -Real.log (562609 / 1000000) ≤ (287585193 / 500000000) := by
  have h := checkLog_sound (w := (437391 / 1562609)) (n := 12)
    (lo := (115034077 / 200000000)) (hi := (287585193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 562609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 562609) = 1/(562609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-287585193 / 500000000) (-115034077 / 200000000) (Real.log (562609 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (22715193 / 62500000) ≤ -Real.log (1000000 / 1438273) ∧
    -Real.log (1000000 / 1438273) ≤ (363443089 / 1000000000) := by
  have h := checkLog_sound (w := (438273 / 2438273)) (n := 12)
    (lo := (22715193 / 62500000)) (hi := (363443089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1438273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1438273 / 1000000) = 1/(1000000 / 1438273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (22715193 / 62500000) (363443089 / 1000000000) (Real.log (1438273 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1438273 / 1000000) = -Real.log (1000000 / 1438273) := by
    rw [show ((1438273 / 1000000) : ℝ) = ((1000000 / 1438273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (36046207 / 62500000) ≤ -Real.log (561727 / 1000000) ∧
    -Real.log (561727 / 1000000) ≤ (576739313 / 1000000000) := by
  have h := checkLog_sound (w := (438273 / 1561727)) (n := 12)
    (lo := (36046207 / 62500000)) (hi := (576739313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 561727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 561727) = 1/(561727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-576739313 / 1000000000) (-36046207 / 62500000) (Real.log (561727 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (141286647 / 500000000) ≤ -Real.log (1000000 / 1326539) ∧
    -Real.log (1000000 / 1326539) ≤ (56514659 / 200000000) := by
  have h := checkLog_sound (w := (326539 / 2326539)) (n := 12)
    (lo := (141286647 / 500000000)) (hi := (56514659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1326539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1326539 / 1000000) = 1/(1000000 / 1326539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (141286647 / 500000000) (56514659 / 200000000) (Real.log (1326539 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1326539 / 1000000) = -Real.log (1000000 / 1326539) := by
    rw [show ((1326539 / 1000000) : ℝ) = ((1000000 / 1326539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (395325191 / 1000000000) ≤ -Real.log (673461 / 1000000) ∧
    -Real.log (673461 / 1000000) ≤ (49415649 / 125000000) := by
  have h := checkLog_sound (w := (326539 / 1673461)) (n := 12)
    (lo := (395325191 / 1000000000)) (hi := (49415649 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 673461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 673461) = 1/(673461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-49415649 / 125000000) (-395325191 / 1000000000) (Real.log (673461 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (141562477 / 500000000) ≤ -Real.log (1000000 / 1327271) ∧
    -Real.log (1000000 / 1327271) ≤ (56624991 / 200000000) := by
  have h := checkLog_sound (w := (327271 / 2327271)) (n := 12)
    (lo := (141562477 / 500000000)) (hi := (56624991 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1327271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1327271 / 1000000) = 1/(1000000 / 1327271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (141562477 / 500000000) (56624991 / 200000000) (Real.log (1327271 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1327271 / 1000000) = -Real.log (1000000 / 1327271) := by
    rw [show ((1327271 / 1000000) : ℝ) = ((1000000 / 1327271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (79282541 / 200000000) ≤ -Real.log (672729 / 1000000) ∧
    -Real.log (672729 / 1000000) ≤ (198206353 / 500000000) := by
  have h := checkLog_sound (w := (327271 / 1672729)) (n := 12)
    (lo := (79282541 / 200000000)) (hi := (198206353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 672729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 672729) = 1/(672729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-198206353 / 500000000) (-79282541 / 200000000) (Real.log (672729 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (18760001 / 20000000) ≤ -Real.log (125000000000 / 319358337673) ∧
    -Real.log (125000000000 / 319358337673) ≤ (234500013 / 250000000) := by
  have h := checkLog_sound (w := (69358337673 / 569358337673)) (n := 12)
    (lo := (24485287 / 100000000)) (hi := (244852871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319358337673 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(319358337673 / 250000000000) = 1/(125000000000 / 319358337673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (18760001 / 20000000) (234500013 / 250000000) (Real.log (319358337673 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (319358337673 / 125000000000) = -Real.log (125000000000 / 319358337673) := by
    rw [show ((319358337673 / 125000000000) : ℝ) = ((125000000000 / 319358337673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (940182399 / 1000000000) ≤ -Real.log (125000000000 / 320056050359) ∧
    -Real.log (125000000000 / 320056050359) ≤ (940182401 / 1000000000) := by
  have h := checkLog_sound (w := (70056050359 / 570056050359)) (n := 12)
    (lo := (247035219 / 1000000000)) (hi := (12351761 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320056050359 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320056050359 / 250000000000) = 1/(125000000000 / 320056050359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (940182399 / 1000000000) (940182401 / 1000000000) (Real.log (320056050359 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (320056050359 / 125000000000) = -Real.log (125000000000 / 320056050359) := by
    rw [show ((320056050359 / 125000000000) : ℝ) = ((125000000000 / 320056050359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (338949243 / 500000000) ≤ -Real.log (500000000000 / 984866978191) ∧
    -Real.log (500000000000 / 984866978191) ≤ (677898487 / 1000000000) := by
  have h := checkLog_sound (w := (484866978191 / 1484866978191)) (n := 12)
    (lo := (338949243 / 500000000)) (hi := (677898487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((984866978191 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(984866978191 / 500000000000) = 1/(500000000000 / 984866978191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (338949243 / 500000000) (677898487 / 1000000000) (Real.log (984866978191 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (984866978191 / 500000000000) = -Real.log (500000000000 / 984866978191) := by
    rw [show ((984866978191 / 500000000000) : ℝ) = ((500000000000 / 984866978191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (679537659 / 1000000000) ≤ -Real.log (250000000000 / 493241334921) ∧
    -Real.log (250000000000 / 493241334921) ≤ (33976883 / 50000000) := by
  have h := checkLog_sound (w := (243241334921 / 743241334921)) (n := 12)
    (lo := (679537659 / 1000000000)) (hi := (33976883 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493241334921 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493241334921 / 250000000000) = 1/(250000000000 / 493241334921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (679537659 / 1000000000) (33976883 / 50000000) (Real.log (493241334921 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (493241334921 / 250000000000) = -Real.log (250000000000 / 493241334921) := by
    rw [show ((493241334921 / 250000000000) : ℝ) = ((250000000000 / 493241334921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0200
