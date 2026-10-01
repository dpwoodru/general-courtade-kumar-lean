import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0030
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

theorem reflection_log_1_neg : (390510087 / 1000000000) ≤ -Real.log (2560 / 3783) ∧
    -Real.log (2560 / 3783) ≤ (48813761 / 125000000) := by
  have h := checkLog_sound (w := (1223 / 6343)) (n := 12)
    (lo := (390510087 / 1000000000)) (hi := (48813761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3783 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3783 / 2560) = 1/(2560 / 3783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (390510087 / 1000000000) (48813761 / 125000000) (Real.log (3783 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3783 / 2560) = -Real.log (2560 / 3783) := by
    rw [show ((3783 / 2560) : ℝ) = ((2560 / 3783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (8119737 / 12500000) ≤ -Real.log (1337 / 2560) ∧
    -Real.log (1337 / 2560) ≤ (649578961 / 1000000000) := by
  have h := checkLog_sound (w := (1223 / 3897)) (n := 12)
    (lo := (8119737 / 12500000)) (hi := (649578961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1337) = 1/(1337 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-649578961 / 1000000000) (-8119737 / 12500000) (Real.log (1337 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (389716751 / 1000000000) ≤ -Real.log (128 / 189) ∧
    -Real.log (128 / 189) ≤ (24357297 / 62500000) := by
  have h := checkLog_sound (w := (61 / 317)) (n := 12)
    (lo := (389716751 / 1000000000)) (hi := (24357297 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189 / 128) = 1/(128 / 189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (389716751 / 1000000000) (24357297 / 62500000) (Real.log (189 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (189 / 128) = -Real.log (128 / 189) := by
    rw [show ((189 / 128) : ℝ) = ((128 / 189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (161834411 / 250000000) ≤ -Real.log (67 / 128) ∧
    -Real.log (67 / 128) ≤ (129467529 / 200000000) := by
  have h := checkLog_sound (w := (61 / 195)) (n := 12)
    (lo := (161834411 / 250000000)) (hi := (129467529 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 67) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 67) = 1/(67 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-129467529 / 200000000) (-161834411 / 250000000) (Real.log (67 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (335314967 / 500000000) ≤ -Real.log (1280 / 2503) ∧
    -Real.log (1280 / 2503) ≤ (134125987 / 200000000) := by
  have h := checkLog_sound (w := (1223 / 3783)) (n := 12)
    (lo := (335314967 / 500000000)) (hi := (134125987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2503 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2503 / 1280) = 1/(1280 / 2503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (335314967 / 500000000) (134125987 / 200000000) (Real.log (2503 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2503 / 1280) = -Real.log (1280 / 2503) := by
    rw [show ((2503 / 1280) : ℝ) = ((1280 / 2503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1555782043 / 500000000) ≤ -Real.log (57 / 1280) ∧
    -Real.log (57 / 1280) ≤ (3111564091 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 57) = 1/(57 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3111564091 / 1000000000) (-1555782043 / 500000000) (Real.log (57 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (669430653 / 1000000000) ≤ -Real.log (64 / 125) ∧
    -Real.log (64 / 125) ≤ (334715327 / 500000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 64) = 1/(64 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (669430653 / 1000000000) (334715327 / 500000000) (Real.log (125 / 64)) := by
  have h := reflection_log_7_neg
  have he : Real.log (125 / 64) = -Real.log (64 / 125) := by
    rw [show ((125 / 64) : ℝ) = ((64 / 125) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (382533849 / 125000000) ≤ -Real.log (3 / 64) ∧
    -Real.log (3 / 64) ≤ (3060270797 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4 / 3) = 1/(3 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3060270797 / 1000000000) (-382533849 / 125000000) (Real.log (3 / 64)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (272062497 / 500000000) ≤ -Real.log (10000 / 17231) ∧
    -Real.log (10000 / 17231) ≤ (108824999 / 200000000) := by
  have h := checkLog_sound (w := (7231 / 27231)) (n := 12)
    (lo := (272062497 / 500000000)) (hi := (108824999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17231 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17231 / 10000) = 1/(10000 / 17231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (272062497 / 500000000) (108824999 / 200000000) (Real.log (17231 / 10000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (17231 / 10000) = -Real.log (10000 / 17231) := by
    rw [show ((17231 / 10000) : ℝ) = ((10000 / 17231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (40128089 / 31250000) ≤ -Real.log (2769 / 10000) ∧
    -Real.log (2769 / 10000) ≤ (25681977 / 20000000) := by
  have h := checkLog_sound (w := (2231 / 7769)) (n := 12)
    (lo := (147737917 / 250000000)) (hi := (590951669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 2769) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5000 / 2769) = 1/(2769 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-25681977 / 20000000) (-40128089 / 31250000) (Real.log (2769 / 10000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (272759011 / 500000000) ≤ -Real.log (500000 / 862751) ∧
    -Real.log (500000 / 862751) ≤ (545518023 / 1000000000) := by
  have h := checkLog_sound (w := (362751 / 1362751)) (n := 12)
    (lo := (272759011 / 500000000)) (hi := (545518023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((862751 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(862751 / 500000) = 1/(500000 / 862751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (272759011 / 500000000) (545518023 / 1000000000) (Real.log (862751 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (862751 / 500000) = -Real.log (500000 / 862751) := by
    rw [show ((862751 / 500000) : ℝ) = ((500000 / 862751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1292811303 / 1000000000) ≤ -Real.log (137249 / 500000) ∧
    -Real.log (137249 / 500000) ≤ (258562261 / 200000000) := by
  have h := checkLog_sound (w := (112751 / 387249)) (n := 12)
    (lo := (599664123 / 1000000000)) (hi := (149916031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 137249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 137249) = 1/(137249 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-258562261 / 200000000) (-1292811303 / 1000000000) (Real.log (137249 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (116899403 / 250000000) ≤ -Real.log (200000 / 319231) ∧
    -Real.log (200000 / 319231) ≤ (467597613 / 1000000000) := by
  have h := checkLog_sound (w := (119231 / 519231)) (n := 12)
    (lo := (116899403 / 250000000)) (hi := (467597613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319231 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319231 / 200000) = 1/(200000 / 319231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (116899403 / 250000000) (467597613 / 1000000000) (Real.log (319231 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (319231 / 200000) = -Real.log (200000 / 319231) := by
    rw [show ((319231 / 200000) : ℝ) = ((200000 / 319231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (906724137 / 1000000000) ≤ -Real.log (80769 / 200000) ∧
    -Real.log (80769 / 200000) ≤ (906724139 / 1000000000) := by
  have h := checkLog_sound (w := (19231 / 180769)) (n := 12)
    (lo := (213576957 / 1000000000)) (hi := (106788479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 80769) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 80769) = 1/(80769 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-906724139 / 1000000000) (-906724137 / 1000000000) (Real.log (80769 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (46923083 / 100000000) ≤ -Real.log (250000 / 399691) ∧
    -Real.log (250000 / 399691) ≤ (469230831 / 1000000000) := by
  have h := checkLog_sound (w := (149691 / 649691)) (n := 12)
    (lo := (46923083 / 100000000)) (hi := (469230831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399691 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399691 / 250000) = 1/(250000 / 399691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (46923083 / 100000000) (469230831 / 1000000000) (Real.log (399691 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (399691 / 250000) = -Real.log (250000 / 399691) := by
    rw [show ((399691 / 250000) : ℝ) = ((250000 / 399691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (182641099 / 200000000) ≤ -Real.log (100309 / 250000) ∧
    -Real.log (100309 / 250000) ≤ (913205497 / 1000000000) := by
  have h := checkLog_sound (w := (24691 / 225309)) (n := 12)
    (lo := (44011663 / 200000000)) (hi := (55014579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100309) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 100309) = 1/(100309 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-913205497 / 1000000000) (-182641099 / 200000000) (Real.log (100309 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1828223841 / 1000000000) ≤ -Real.log (125000000000 / 777853015529) ∧
    -Real.log (125000000000 / 777853015529) ≤ (457055961 / 250000000) := by
  have h := checkLog_sound (w := (277853015529 / 1277853015529)) (n := 12)
    (lo := (441929481 / 1000000000)) (hi := (220964741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777853015529 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(777853015529 / 500000000000) = 1/(125000000000 / 777853015529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1828223841 / 1000000000) (457055961 / 250000000) (Real.log (777853015529 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (777853015529 / 125000000000) = -Real.log (125000000000 / 777853015529) := by
    rw [show ((777853015529 / 125000000000) : ℝ) = ((125000000000 / 777853015529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (73533173 / 40000000) ≤ -Real.log (500000000000 / 3143013792451) ∧
    -Real.log (500000000000 / 3143013792451) ≤ (114895583 / 62500000) := by
  have h := checkLog_sound (w := (1143013792451 / 5143013792451)) (n := 12)
    (lo := (90406993 / 200000000)) (hi := (226017483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3143013792451 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3143013792451 / 2000000000000) = 1/(500000000000 / 3143013792451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (73533173 / 40000000) (114895583 / 62500000) (Real.log (3143013792451 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3143013792451 / 500000000000) = -Real.log (500000000000 / 3143013792451) := by
    rw [show ((3143013792451 / 500000000000) : ℝ) = ((500000000000 / 3143013792451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1374321749 / 1000000000) ≤ -Real.log (1562500000 / 6175617347) ∧
    -Real.log (1562500000 / 6175617347) ≤ (1374321751 / 1000000000) := by
  have h := checkLog_sound (w := (3050617347 / 9300617347)) (n := 12)
    (lo := (681174569 / 1000000000)) (hi := (68117457 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6175617347 / 3125000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6175617347 / 3125000000) = 1/(1562500000 / 6175617347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1374321749 / 1000000000) (1374321751 / 1000000000) (Real.log (6175617347 / 1562500000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6175617347 / 1562500000) = -Real.log (1562500000 / 6175617347) := by
    rw [show ((6175617347 / 1562500000) : ℝ) = ((1562500000 / 6175617347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (691218163 / 500000000) ≤ -Real.log (500000000000 / 1992298796719) ∧
    -Real.log (500000000000 / 1992298796719) ≤ (172804541 / 125000000) := by
  have h := checkLog_sound (w := (992298796719 / 2992298796719)) (n := 12)
    (lo := (344644573 / 500000000)) (hi := (689289147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1992298796719 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1992298796719 / 1000000000000) = 1/(500000000000 / 1992298796719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (691218163 / 500000000) (172804541 / 125000000) (Real.log (1992298796719 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1992298796719 / 500000000000) = -Real.log (500000000000 / 1992298796719) := by
    rw [show ((1992298796719 / 500000000000) : ℝ) = ((500000000000 / 1992298796719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0030
