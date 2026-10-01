import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0288
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

theorem reflection_log_1_neg : (226730859 / 1000000000) ≤ -Real.log (5120 / 6423) ∧
    -Real.log (5120 / 6423) ≤ (11336543 / 50000000) := by
  have h := checkLog_sound (w := (1303 / 11543)) (n := 12)
    (lo := (226730859 / 1000000000)) (hi := (11336543 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6423 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6423 / 5120) = 1/(5120 / 6423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (226730859 / 1000000000) (11336543 / 50000000) (Real.log (6423 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6423 / 5120) = -Real.log (5120 / 6423) := by
    rw [show ((6423 / 5120) : ℝ) = ((5120 / 6423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (58737933 / 200000000) ≤ -Real.log (3817 / 5120) ∧
    -Real.log (3817 / 5120) ≤ (146844833 / 500000000) := by
  have h := checkLog_sound (w := (1303 / 8937)) (n := 12)
    (lo := (58737933 / 200000000)) (hi := (146844833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3817) = 1/(3817 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-146844833 / 500000000) (-58737933 / 200000000) (Real.log (3817 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (14156081 / 62500000) ≤ -Real.log (10240 / 12843) ∧
    -Real.log (10240 / 12843) ≤ (226497297 / 1000000000) := by
  have h := checkLog_sound (w := (2603 / 23083)) (n := 12)
    (lo := (14156081 / 62500000)) (hi := (226497297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12843 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12843 / 10240) = 1/(10240 / 12843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (14156081 / 62500000) (226497297 / 1000000000) (Real.log (12843 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12843 / 10240) = -Real.log (10240 / 12843) := by
    rw [show ((12843 / 10240) : ℝ) = ((10240 / 12843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (293296763 / 1000000000) ≤ -Real.log (7637 / 10240) ∧
    -Real.log (7637 / 10240) ≤ (73324191 / 250000000) := by
  have h := checkLog_sound (w := (2603 / 17877)) (n := 12)
    (lo := (293296763 / 1000000000)) (hi := (73324191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7637) = 1/(7637 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-73324191 / 250000000) (-293296763 / 1000000000) (Real.log (7637 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (16457473 / 40000000) ≤ -Real.log (2560 / 3863) ∧
    -Real.log (2560 / 3863) ≤ (205718413 / 500000000) := by
  have h := checkLog_sound (w := (1303 / 6423)) (n := 12)
    (lo := (16457473 / 40000000)) (hi := (205718413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3863 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3863 / 2560) = 1/(2560 / 3863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (16457473 / 40000000) (205718413 / 500000000) (Real.log (3863 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3863 / 2560) = -Real.log (2560 / 3863) := by
    rw [show ((3863 / 2560) : ℝ) = ((2560 / 3863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (22227479 / 31250000) ≤ -Real.log (1257 / 2560) ∧
    -Real.log (1257 / 2560) ≤ (71127933 / 100000000) := by
  have h := checkLog_sound (w := (23 / 2537)) (n := 12)
    (lo := (4533037 / 250000000)) (hi := (18132149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1257) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1257) = 1/(1257 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-71127933 / 100000000) (-22227479 / 31250000) (Real.log (1257 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (8220969 / 20000000) ≤ -Real.log (5120 / 7723) ∧
    -Real.log (5120 / 7723) ≤ (411048451 / 1000000000) := by
  have h := checkLog_sound (w := (2603 / 12843)) (n := 12)
    (lo := (8220969 / 20000000)) (hi := (411048451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7723 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7723 / 5120) = 1/(5120 / 7723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (8220969 / 20000000) (411048451 / 1000000000) (Real.log (7723 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7723 / 5120) = -Real.log (5120 / 7723) := by
    rw [show ((7723 / 5120) : ℝ) = ((5120 / 7723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (355043361 / 500000000) ≤ -Real.log (2517 / 5120) ∧
    -Real.log (2517 / 5120) ≤ (177521681 / 250000000) := by
  have h := checkLog_sound (w := (43 / 5077)) (n := 12)
    (lo := (8469771 / 500000000)) (hi := (16939543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2517) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2517) = 1/(2517 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-177521681 / 250000000) (-355043361 / 500000000) (Real.log (2517 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (310309383 / 1000000000) ≤ -Real.log (1000000 / 1363847) ∧
    -Real.log (1000000 / 1363847) ≤ (38788673 / 125000000) := by
  have h := checkLog_sound (w := (363847 / 2363847)) (n := 12)
    (lo := (310309383 / 1000000000)) (hi := (38788673 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1363847 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1363847 / 1000000) = 1/(1000000 / 1363847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (310309383 / 1000000000) (38788673 / 125000000) (Real.log (1363847 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1363847 / 1000000) = -Real.log (1000000 / 1363847) := by
    rw [show ((1363847 / 1000000) : ℝ) = ((1000000 / 1363847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (226158089 / 500000000) ≤ -Real.log (636153 / 1000000) ∧
    -Real.log (636153 / 1000000) ≤ (452316179 / 1000000000) := by
  have h := checkLog_sound (w := (363847 / 1636153)) (n := 12)
    (lo := (226158089 / 500000000)) (hi := (452316179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 636153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 636153) = 1/(636153 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-452316179 / 1000000000) (-226158089 / 500000000) (Real.log (636153 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (310626083 / 1000000000) ≤ -Real.log (1000000 / 1364279) ∧
    -Real.log (1000000 / 1364279) ≤ (77656521 / 250000000) := by
  have h := checkLog_sound (w := (364279 / 2364279)) (n := 12)
    (lo := (310626083 / 1000000000)) (hi := (77656521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1364279 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1364279 / 1000000) = 1/(1000000 / 1364279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (310626083 / 1000000000) (77656521 / 250000000) (Real.log (1364279 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1364279 / 1000000) = -Real.log (1000000 / 1364279) := by
    rw [show ((1364279 / 1000000) : ℝ) = ((1000000 / 1364279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (452995491 / 1000000000) ≤ -Real.log (635721 / 1000000) ∧
    -Real.log (635721 / 1000000) ≤ (113248873 / 250000000) := by
  have h := checkLog_sound (w := (364279 / 1635721)) (n := 12)
    (lo := (452995491 / 1000000000)) (hi := (113248873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 635721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 635721) = 1/(635721 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-113248873 / 250000000) (-452995491 / 1000000000) (Real.log (635721 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (118349233 / 500000000) ≤ -Real.log (1000000 / 1267059) ∧
    -Real.log (1000000 / 1267059) ≤ (236698467 / 1000000000) := by
  have h := checkLog_sound (w := (267059 / 2267059)) (n := 12)
    (lo := (118349233 / 500000000)) (hi := (236698467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267059 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267059 / 1000000) = 1/(1000000 / 1267059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (118349233 / 500000000) (236698467 / 1000000000) (Real.log (1267059 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1267059 / 1000000) = -Real.log (1000000 / 1267059) := by
    rw [show ((1267059 / 1000000) : ℝ) = ((1000000 / 1267059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (310690071 / 1000000000) ≤ -Real.log (732941 / 1000000) ∧
    -Real.log (732941 / 1000000) ≤ (38836259 / 125000000) := by
  have h := checkLog_sound (w := (267059 / 1732941)) (n := 12)
    (lo := (310690071 / 1000000000)) (hi := (38836259 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732941) = 1/(732941 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-38836259 / 125000000) (-310690071 / 1000000000) (Real.log (732941 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (236967557 / 1000000000) ≤ -Real.log (5000 / 6337) ∧
    -Real.log (5000 / 6337) ≤ (118483779 / 500000000) := by
  have h := checkLog_sound (w := (1337 / 11337)) (n := 12)
    (lo := (236967557 / 1000000000)) (hi := (118483779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6337 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6337 / 5000) = 1/(5000 / 6337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (236967557 / 1000000000) (118483779 / 500000000) (Real.log (6337 / 5000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (6337 / 5000) = -Real.log (5000 / 6337) := by
    rw [show ((6337 / 5000) : ℝ) = ((5000 / 6337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (77788857 / 250000000) ≤ -Real.log (3663 / 5000) ∧
    -Real.log (3663 / 5000) ≤ (311155429 / 1000000000) := by
  have h := checkLog_sound (w := (1337 / 8663)) (n := 12)
    (lo := (77788857 / 250000000)) (hi := (311155429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 3663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 3663) = 1/(3663 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-311155429 / 1000000000) (-77788857 / 250000000) (Real.log (3663 / 5000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (762625561 / 1000000000) ≤ -Real.log (50000000000 / 107194888651) ∧
    -Real.log (50000000000 / 107194888651) ≤ (762625563 / 1000000000) := by
  have h := checkLog_sound (w := (7194888651 / 207194888651)) (n := 12)
    (lo := (69478381 / 1000000000)) (hi := (34739191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107194888651 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(107194888651 / 100000000000) = 1/(50000000000 / 107194888651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (762625561 / 1000000000) (762625563 / 1000000000) (Real.log (107194888651 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (107194888651 / 50000000000) = -Real.log (50000000000 / 107194888651) := by
    rw [show ((107194888651 / 50000000000) : ℝ) = ((50000000000 / 107194888651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (381810787 / 500000000) ≤ -Real.log (500000000000 / 1073017093977) ∧
    -Real.log (500000000000 / 1073017093977) ≤ (95452697 / 125000000) := by
  have h := checkLog_sound (w := (73017093977 / 2073017093977)) (n := 12)
    (lo := (35237197 / 500000000)) (hi := (14094879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1073017093977 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1073017093977 / 1000000000000) = 1/(500000000000 / 1073017093977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (381810787 / 500000000) (95452697 / 125000000) (Real.log (1073017093977 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1073017093977 / 500000000000) = -Real.log (500000000000 / 1073017093977) := by
    rw [show ((1073017093977 / 500000000000) : ℝ) = ((500000000000 / 1073017093977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (273694269 / 500000000) ≤ -Real.log (250000000000 / 432183149803) ∧
    -Real.log (250000000000 / 432183149803) ≤ (547388539 / 1000000000) := by
  have h := checkLog_sound (w := (182183149803 / 682183149803)) (n := 12)
    (lo := (273694269 / 500000000)) (hi := (547388539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432183149803 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(432183149803 / 250000000000) = 1/(250000000000 / 432183149803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (273694269 / 500000000) (547388539 / 1000000000) (Real.log (432183149803 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (432183149803 / 250000000000) = -Real.log (250000000000 / 432183149803) := by
    rw [show ((432183149803 / 250000000000) : ℝ) = ((250000000000 / 432183149803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (274061493 / 500000000) ≤ -Real.log (250000000000 / 432500682501) ∧
    -Real.log (250000000000 / 432500682501) ≤ (548122987 / 1000000000) := by
  have h := checkLog_sound (w := (182500682501 / 682500682501)) (n := 12)
    (lo := (274061493 / 500000000)) (hi := (548122987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432500682501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(432500682501 / 250000000000) = 1/(250000000000 / 432500682501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (274061493 / 500000000) (548122987 / 1000000000) (Real.log (432500682501 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (432500682501 / 250000000000) = -Real.log (250000000000 / 432500682501) := by
    rw [show ((432500682501 / 250000000000) : ℝ) = ((250000000000 / 432500682501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0288
