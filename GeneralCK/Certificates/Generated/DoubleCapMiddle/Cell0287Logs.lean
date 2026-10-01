import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0287
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

theorem reflection_log_1_neg : (226964367 / 1000000000) ≤ -Real.log (10240 / 12849) ∧
    -Real.log (10240 / 12849) ≤ (14185273 / 62500000) := by
  have h := checkLog_sound (w := (2609 / 23089)) (n := 12)
    (lo := (226964367 / 1000000000)) (hi := (14185273 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12849 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12849 / 10240) = 1/(10240 / 12849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (226964367 / 1000000000) (14185273 / 62500000) (Real.log (12849 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12849 / 10240) = -Real.log (10240 / 12849) := by
    rw [show ((12849 / 10240) : ℝ) = ((10240 / 12849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (294082721 / 1000000000) ≤ -Real.log (7631 / 10240) ∧
    -Real.log (7631 / 10240) ≤ (147041361 / 500000000) := by
  have h := checkLog_sound (w := (2609 / 17871)) (n := 12)
    (lo := (294082721 / 1000000000)) (hi := (147041361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7631) = 1/(7631 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-147041361 / 500000000) (-294082721 / 1000000000) (Real.log (7631 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (226730859 / 1000000000) ≤ -Real.log (5120 / 6423) ∧
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


theorem reflection_log_3 : Bounds (226730859 / 1000000000) (11336543 / 50000000) (Real.log (6423 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6423 / 5120) = -Real.log (5120 / 6423) := by
    rw [show ((6423 / 5120) : ℝ) = ((5120 / 6423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (58737933 / 200000000) ≤ -Real.log (3817 / 5120) ∧
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


theorem reflection_log_4 : Bounds (-146844833 / 500000000) (-58737933 / 200000000) (Real.log (3817 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (411825049 / 1000000000) ≤ -Real.log (5120 / 7729) ∧
    -Real.log (5120 / 7729) ≤ (8236501 / 20000000) := by
  have h := checkLog_sound (w := (2609 / 12849)) (n := 12)
    (lo := (411825049 / 1000000000)) (hi := (8236501 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7729 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7729 / 5120) = 1/(5120 / 7729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (411825049 / 1000000000) (8236501 / 20000000) (Real.log (7729 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7729 / 5120) = -Real.log (5120 / 7729) := by
    rw [show ((7729 / 5120) : ℝ) = ((5120 / 7729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (356236679 / 500000000) ≤ -Real.log (2511 / 5120) ∧
    -Real.log (2511 / 5120) ≤ (8905917 / 12500000) := by
  have h := checkLog_sound (w := (49 / 5071)) (n := 12)
    (lo := (9663089 / 500000000)) (hi := (19326179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2511) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2511) = 1/(2511 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-8905917 / 12500000) (-356236679 / 500000000) (Real.log (2511 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (16457473 / 40000000) ≤ -Real.log (2560 / 3863) ∧
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


theorem reflection_log_7 : Bounds (16457473 / 40000000) (205718413 / 500000000) (Real.log (3863 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3863 / 2560) = -Real.log (2560 / 3863) := by
    rw [show ((3863 / 2560) : ℝ) = ((2560 / 3863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (22227479 / 31250000) ≤ -Real.log (1257 / 2560) ∧
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


theorem reflection_log_8 : Bounds (-71127933 / 100000000) (-22227479 / 31250000) (Real.log (1257 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (6212507 / 20000000) ≤ -Real.log (500000 / 682139) ∧
    -Real.log (500000 / 682139) ≤ (310625351 / 1000000000) := by
  have h := checkLog_sound (w := (182139 / 1182139)) (n := 12)
    (lo := (6212507 / 20000000)) (hi := (310625351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682139 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682139 / 500000) = 1/(500000 / 682139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (6212507 / 20000000) (310625351 / 1000000000) (Real.log (682139 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (682139 / 500000) = -Real.log (500000 / 682139) := by
    rw [show ((682139 / 500000) : ℝ) = ((500000 / 682139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (226496959 / 500000000) ≤ -Real.log (317861 / 500000) ∧
    -Real.log (317861 / 500000) ≤ (452993919 / 1000000000) := by
  have h := checkLog_sound (w := (182139 / 817861)) (n := 12)
    (lo := (226496959 / 500000000)) (hi := (452993919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 317861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 317861) = 1/(317861 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-452993919 / 1000000000) (-226496959 / 500000000) (Real.log (317861 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (310941951 / 1000000000) ≤ -Real.log (100000 / 136471) ∧
    -Real.log (100000 / 136471) ≤ (1214617 / 3906250) := by
  have h := checkLog_sound (w := (36471 / 236471)) (n := 12)
    (lo := (310941951 / 1000000000)) (hi := (1214617 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136471 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136471 / 100000) = 1/(100000 / 136471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (310941951 / 1000000000) (1214617 / 3906250) (Real.log (136471 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (136471 / 100000) = -Real.log (100000 / 136471) := by
    rw [show ((136471 / 100000) : ℝ) = ((100000 / 136471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (453673691 / 1000000000) ≤ -Real.log (63529 / 100000) ∧
    -Real.log (63529 / 100000) ≤ (113418423 / 250000000) := by
  have h := checkLog_sound (w := (36471 / 163529)) (n := 12)
    (lo := (453673691 / 1000000000)) (hi := (113418423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 63529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 63529) = 1/(63529 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-113418423 / 250000000) (-453673691 / 1000000000) (Real.log (63529 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (14810423 / 62500000) ≤ -Real.log (1000000 / 1267399) ∧
    -Real.log (1000000 / 1267399) ≤ (236966769 / 1000000000) := by
  have h := checkLog_sound (w := (267399 / 2267399)) (n := 12)
    (lo := (14810423 / 62500000)) (hi := (236966769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267399 / 1000000) = 1/(1000000 / 1267399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (14810423 / 62500000) (236966769 / 1000000000) (Real.log (1267399 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1267399 / 1000000) = -Real.log (1000000 / 1267399) := by
    rw [show ((1267399 / 1000000) : ℝ) = ((1000000 / 1267399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (311154063 / 1000000000) ≤ -Real.log (732601 / 1000000) ∧
    -Real.log (732601 / 1000000) ≤ (19447129 / 62500000) := by
  have h := checkLog_sound (w := (267399 / 1732601)) (n := 12)
    (lo := (311154063 / 1000000000)) (hi := (19447129 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732601) = 1/(732601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-19447129 / 62500000) (-311154063 / 1000000000) (Real.log (732601 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (237235787 / 1000000000) ≤ -Real.log (50000 / 63387) ∧
    -Real.log (50000 / 63387) ≤ (59308947 / 250000000) := by
  have h := checkLog_sound (w := (13387 / 113387)) (n := 12)
    (lo := (237235787 / 1000000000)) (hi := (59308947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63387 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63387 / 50000) = 1/(50000 / 63387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (237235787 / 1000000000) (59308947 / 250000000) (Real.log (63387 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (63387 / 50000) = -Real.log (50000 / 63387) := by
    rw [show ((63387 / 50000) : ℝ) = ((50000 / 63387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (77904909 / 250000000) ≤ -Real.log (36613 / 50000) ∧
    -Real.log (36613 / 50000) ≤ (311619637 / 1000000000) := by
  have h := checkLog_sound (w := (13387 / 86613)) (n := 12)
    (lo := (77904909 / 250000000)) (hi := (311619637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 36613) = 1/(36613 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-311619637 / 1000000000) (-77904909 / 250000000) (Real.log (36613 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (190904817 / 250000000) ≤ -Real.log (500000000000 / 1073014619597) ∧
    -Real.log (500000000000 / 1073014619597) ≤ (76361927 / 100000000) := by
  have h := checkLog_sound (w := (73014619597 / 2073014619597)) (n := 12)
    (lo := (8809011 / 125000000)) (hi := (70472089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1073014619597 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1073014619597 / 1000000000000) = 1/(500000000000 / 1073014619597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (190904817 / 250000000) (76361927 / 100000000) (Real.log (1073014619597 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1073014619597 / 500000000000) = -Real.log (500000000000 / 1073014619597) := by
    rw [show ((1073014619597 / 500000000000) : ℝ) = ((500000000000 / 1073014619597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (382307821 / 500000000) ≤ -Real.log (500000000000 / 1074084276473) ∧
    -Real.log (500000000000 / 1074084276473) ≤ (191153911 / 250000000) := by
  have h := checkLog_sound (w := (74084276473 / 2074084276473)) (n := 12)
    (lo := (35734231 / 500000000)) (hi := (71468463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1074084276473 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1074084276473 / 1000000000000) = 1/(500000000000 / 1074084276473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (382307821 / 500000000) (191153911 / 250000000) (Real.log (1074084276473 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1074084276473 / 500000000000) = -Real.log (500000000000 / 1074084276473) := by
    rw [show ((1074084276473 / 500000000000) : ℝ) = ((500000000000 / 1074084276473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2141097 / 3906250) ≤ -Real.log (20000000000 / 34599980071) ∧
    -Real.log (20000000000 / 34599980071) ≤ (548120833 / 1000000000) := by
  have h := checkLog_sound (w := (14599980071 / 54599980071)) (n := 12)
    (lo := (2141097 / 3906250)) (hi := (548120833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34599980071 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34599980071 / 20000000000) = 1/(20000000000 / 34599980071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2141097 / 3906250) (548120833 / 1000000000) (Real.log (34599980071 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (34599980071 / 20000000000) = -Real.log (20000000000 / 34599980071) := by
    rw [show ((34599980071 / 20000000000) : ℝ) = ((20000000000 / 34599980071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4287933 / 7812500) ≤ -Real.log (31250000000 / 54102197307) ∧
    -Real.log (31250000000 / 54102197307) ≤ (21954217 / 40000000) := by
  have h := checkLog_sound (w := (22852197307 / 85352197307)) (n := 12)
    (lo := (4287933 / 7812500)) (hi := (21954217 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54102197307 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54102197307 / 31250000000) = 1/(31250000000 / 54102197307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4287933 / 7812500) (21954217 / 40000000) (Real.log (54102197307 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (54102197307 / 31250000000) = -Real.log (31250000000 / 54102197307) := by
    rw [show ((54102197307 / 31250000000) : ℝ) = ((31250000000 / 54102197307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0287
