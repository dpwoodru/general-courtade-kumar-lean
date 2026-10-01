import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0070
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

theorem reflection_log_1_neg : (14331009 / 40000000) ≤ -Real.log (2560 / 3663) ∧
    -Real.log (2560 / 3663) ≤ (179137613 / 500000000) := by
  have h := checkLog_sound (w := (1103 / 6223)) (n := 12)
    (lo := (14331009 / 40000000)) (hi := (179137613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3663 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3663 / 2560) = 1/(2560 / 3663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (14331009 / 40000000) (179137613 / 500000000) (Real.log (3663 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3663 / 2560) = -Real.log (2560 / 3663) := by
    rw [show ((3663 / 2560) : ℝ) = ((2560 / 3663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (563627731 / 1000000000) ≤ -Real.log (1457 / 2560) ∧
    -Real.log (1457 / 2560) ≤ (140906933 / 250000000) := by
  have h := checkLog_sound (w := (1103 / 4017)) (n := 12)
    (lo := (563627731 / 1000000000)) (hi := (140906933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1457) = 1/(1457 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-140906933 / 250000000) (-563627731 / 1000000000) (Real.log (1457 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (22340993 / 62500000) ≤ -Real.log (128 / 183) ∧
    -Real.log (128 / 183) ≤ (357455889 / 1000000000) := by
  have h := checkLog_sound (w := (55 / 311)) (n := 12)
    (lo := (22340993 / 62500000)) (hi := (357455889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183 / 128) = 1/(128 / 183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (22340993 / 62500000) (357455889 / 1000000000) (Real.log (183 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (183 / 128) = -Real.log (128 / 183) := by
    rw [show ((183 / 128) : ℝ) = ((128 / 183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (280785411 / 500000000) ≤ -Real.log (73 / 128) ∧
    -Real.log (73 / 128) ≤ (561570823 / 1000000000) := by
  have h := checkLog_sound (w := (55 / 201)) (n := 12)
    (lo := (280785411 / 500000000)) (hi := (561570823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 73) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 73) = 1/(73 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-561570823 / 1000000000) (-280785411 / 500000000) (Real.log (73 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (15537503 / 25000000) ≤ -Real.log (1280 / 2383) ∧
    -Real.log (1280 / 2383) ≤ (621500121 / 1000000000) := by
  have h := checkLog_sound (w := (1103 / 3663)) (n := 12)
    (lo := (15537503 / 25000000)) (hi := (621500121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2383 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2383 / 1280) = 1/(1280 / 2383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (15537503 / 25000000) (621500121 / 1000000000) (Real.log (2383 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2383 / 1280) = -Real.log (1280 / 2383) := by
    rw [show ((2383 / 1280) : ℝ) = ((1280 / 2383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1978465623 / 1000000000) ≤ -Real.log (177 / 1280) ∧
    -Real.log (177 / 1280) ≤ (989232813 / 500000000) := by
  have h := checkLog_sound (w := (143 / 497)) (n := 12)
    (lo := (592171263 / 1000000000)) (hi := (2313169 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 177) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 177) = 1/(177 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-989232813 / 500000000) (-1978465623 / 1000000000) (Real.log (177 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (620240409 / 1000000000) ≤ -Real.log (64 / 119) ∧
    -Real.log (64 / 119) ≤ (62024041 / 100000000) := by
  have h := checkLog_sound (w := (55 / 183)) (n := 12)
    (lo := (620240409 / 1000000000)) (hi := (62024041 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119 / 64) = 1/(64 / 119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (620240409 / 1000000000) (62024041 / 100000000) (Real.log (119 / 64)) := by
  have h := reflection_log_7_neg
  have he : Real.log (119 / 64) = -Real.log (64 / 119) := by
    rw [show ((119 / 64) : ℝ) = ((64 / 119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (245207313 / 125000000) ≤ -Real.log (9 / 64) ∧
    -Real.log (9 / 64) ≤ (1961658507 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(16 / 9) = 1/(9 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1961658507 / 1000000000) (-245207313 / 125000000) (Real.log (9 / 64)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (492754113 / 1000000000) ≤ -Real.log (500000 / 818409) ∧
    -Real.log (500000 / 818409) ≤ (246377057 / 500000000) := by
  have h := checkLog_sound (w := (318409 / 1318409)) (n := 12)
    (lo := (492754113 / 1000000000)) (hi := (246377057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((818409 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(818409 / 500000) = 1/(500000 / 818409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (492754113 / 1000000000) (246377057 / 500000000) (Real.log (818409 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (818409 / 500000) = -Real.log (500000 / 818409) := by
    rw [show ((818409 / 500000) : ℝ) = ((500000 / 818409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (126606399 / 125000000) ≤ -Real.log (181591 / 500000) ∧
    -Real.log (181591 / 500000) ≤ (506425597 / 500000000) := by
  have h := checkLog_sound (w := (68409 / 431591)) (n := 12)
    (lo := (79926003 / 250000000)) (hi := (319704013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 181591) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 181591) = 1/(181591 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-506425597 / 500000000) (-126606399 / 125000000) (Real.log (181591 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (246991591 / 500000000) ≤ -Real.log (1000000 / 1638831) ∧
    -Real.log (1000000 / 1638831) ≤ (493983183 / 1000000000) := by
  have h := checkLog_sound (w := (638831 / 2638831)) (n := 12)
    (lo := (246991591 / 500000000)) (hi := (493983183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1638831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1638831 / 1000000) = 1/(1000000 / 1638831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (246991591 / 500000000) (493983183 / 1000000000) (Real.log (1638831 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1638831 / 1000000) = -Real.log (1000000 / 1638831) := by
    rw [show ((1638831 / 1000000) : ℝ) = ((1000000 / 1638831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (203681857 / 200000000) ≤ -Real.log (361169 / 1000000) ∧
    -Real.log (361169 / 1000000) ≤ (1018409287 / 1000000000) := by
  have h := checkLog_sound (w := (138831 / 861169)) (n := 12)
    (lo := (65052421 / 200000000)) (hi := (162631053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 361169) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 361169) = 1/(361169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1018409287 / 1000000000) (-203681857 / 200000000) (Real.log (361169 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (102471331 / 250000000) ≤ -Real.log (200000 / 301329) ∧
    -Real.log (200000 / 301329) ≤ (16395413 / 40000000) := by
  have h := checkLog_sound (w := (101329 / 501329)) (n := 12)
    (lo := (102471331 / 250000000)) (hi := (16395413 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301329 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301329 / 200000) = 1/(200000 / 301329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (102471331 / 250000000) (16395413 / 40000000) (Real.log (301329 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (301329 / 200000) = -Real.log (200000 / 301329) := by
    rw [show ((301329 / 200000) : ℝ) = ((200000 / 301329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (353263141 / 500000000) ≤ -Real.log (98671 / 200000) ∧
    -Real.log (98671 / 200000) ≤ (176631571 / 250000000) := by
  have h := checkLog_sound (w := (1329 / 198671)) (n := 12)
    (lo := (6689551 / 500000000)) (hi := (13379103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 98671) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 98671) = 1/(98671 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-176631571 / 250000000) (-353263141 / 500000000) (Real.log (98671 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (102802477 / 250000000) ≤ -Real.log (500000 / 754321) ∧
    -Real.log (500000 / 754321) ≤ (411209909 / 1000000000) := by
  have h := checkLog_sound (w := (254321 / 1254321)) (n := 12)
    (lo := (102802477 / 250000000)) (hi := (411209909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754321 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754321 / 500000) = 1/(500000 / 754321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (102802477 / 250000000) (411209909 / 1000000000) (Real.log (754321 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (754321 / 500000) = -Real.log (500000 / 754321) := by
    rw [show ((754321 / 500000) : ℝ) = ((500000 / 754321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (177645573 / 250000000) ≤ -Real.log (245679 / 500000) ∧
    -Real.log (245679 / 500000) ≤ (355291147 / 500000000) := by
  have h := checkLog_sound (w := (4321 / 495679)) (n := 12)
    (lo := (2179389 / 125000000)) (hi := (17435113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 245679) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 245679) = 1/(245679 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-355291147 / 500000000) (-177645573 / 250000000) (Real.log (245679 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (301121061 / 200000000) ≤ -Real.log (500000000000 / 2253440423809) ∧
    -Real.log (500000000000 / 2253440423809) ≤ (376401327 / 250000000) := by
  have h := checkLog_sound (w := (253440423809 / 4253440423809)) (n := 12)
    (lo := (23862189 / 200000000)) (hi := (59655473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2253440423809 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2253440423809 / 2000000000000) = 1/(500000000000 / 2253440423809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (301121061 / 200000000) (376401327 / 250000000) (Real.log (2253440423809 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2253440423809 / 500000000000) = -Real.log (500000000000 / 2253440423809) := by
    rw [show ((2253440423809 / 500000000000) : ℝ) = ((500000000000 / 2253440423809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1512392467 / 1000000000) ≤ -Real.log (500000000000 / 2268786911391) ∧
    -Real.log (500000000000 / 2268786911391) ≤ (151239247 / 100000000) := by
  have h := checkLog_sound (w := (268786911391 / 4268786911391)) (n := 12)
    (lo := (126098107 / 1000000000)) (hi := (31524527 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2268786911391 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2268786911391 / 2000000000000) = 1/(500000000000 / 2268786911391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1512392467 / 1000000000) (151239247 / 100000000) (Real.log (2268786911391 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2268786911391 / 500000000000) = -Real.log (500000000000 / 2268786911391) := by
    rw [show ((2268786911391 / 500000000000) : ℝ) = ((500000000000 / 2268786911391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (558205803 / 500000000) ≤ -Real.log (500000000000 / 1526938006101) ∧
    -Real.log (500000000000 / 1526938006101) ≤ (139551451 / 125000000) := by
  have h := checkLog_sound (w := (526938006101 / 2526938006101)) (n := 12)
    (lo := (211632213 / 500000000)) (hi := (423264427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1526938006101 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1526938006101 / 1000000000000) = 1/(500000000000 / 1526938006101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (558205803 / 500000000) (139551451 / 125000000) (Real.log (1526938006101 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1526938006101 / 500000000000) = -Real.log (500000000000 / 1526938006101) := by
    rw [show ((1526938006101 / 500000000000) : ℝ) = ((500000000000 / 1526938006101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (5608961 / 5000000) ≤ -Real.log (125000000000 / 383793995417) ∧
    -Real.log (125000000000 / 383793995417) ≤ (560896101 / 500000000) := by
  have h := checkLog_sound (w := (133793995417 / 633793995417)) (n := 12)
    (lo := (21432251 / 50000000)) (hi := (428645021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383793995417 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(383793995417 / 250000000000) = 1/(125000000000 / 383793995417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (5608961 / 5000000) (560896101 / 500000000) (Real.log (383793995417 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (383793995417 / 125000000000) = -Real.log (125000000000 / 383793995417) := by
    rw [show ((383793995417 / 125000000000) : ℝ) = ((125000000000 / 383793995417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0070
