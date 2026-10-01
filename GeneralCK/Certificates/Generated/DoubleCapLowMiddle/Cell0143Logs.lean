import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0143
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

theorem reflection_log_1_neg : (657277097 / 1000000000) ≤ -Real.log (6400 / 12349) ∧
    -Real.log (6400 / 12349) ≤ (328638549 / 500000000) := by
  have h := checkLog_sound (w := (5949 / 18749)) (n := 12)
    (lo := (657277097 / 1000000000)) (hi := (328638549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12349 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12349 / 6400) = 1/(6400 / 12349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (657277097 / 1000000000) (328638549 / 500000000) (Real.log (12349 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12349 / 6400) = -Real.log (6400 / 12349) := by
    rw [show ((12349 / 6400) : ℝ) = ((6400 / 12349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (331573241 / 125000000) ≤ -Real.log (451 / 6400) ∧
    -Real.log (451 / 6400) ≤ (663146483 / 250000000) := by
  have h := checkLog_sound (w := (349 / 1251)) (n := 12)
    (lo := (143286097 / 250000000)) (hi := (573144389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 451) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 451) = 1/(451 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-663146483 / 250000000) (-331573241 / 125000000) (Real.log (451 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (656892377 / 1000000000) ≤ -Real.log (25600 / 49377) ∧
    -Real.log (25600 / 49377) ≤ (328446189 / 500000000) := by
  have h := checkLog_sound (w := (23777 / 74977)) (n := 12)
    (lo := (656892377 / 1000000000)) (hi := (328446189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49377 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49377 / 25600) = 1/(25600 / 49377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (656892377 / 1000000000) (328446189 / 500000000) (Real.log (49377 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49377 / 25600) = -Real.log (25600 / 49377) := by
    rw [show ((49377 / 25600) : ℝ) = ((25600 / 49377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1321054427 / 500000000) ≤ -Real.log (1823 / 25600) ∧
    -Real.log (1823 / 25600) ≤ (1321054429 / 500000000) := by
  have h := checkLog_sound (w := (1377 / 5023)) (n := 12)
    (lo := (281333657 / 500000000)) (hi := (112533463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1823) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1823) = 1/(1823 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1321054429 / 500000000) (-1321054427 / 500000000) (Real.log (1823 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (77509041 / 125000000) ≤ -Real.log (3200 / 5949) ∧
    -Real.log (3200 / 5949) ≤ (620072329 / 1000000000) := by
  have h := checkLog_sound (w := (2749 / 9149)) (n := 12)
    (lo := (77509041 / 125000000)) (hi := (620072329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5949 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5949 / 3200) = 1/(3200 / 5949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (77509041 / 125000000) (620072329 / 1000000000) (Real.log (5949 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5949 / 3200) = -Real.log (3200 / 5949) := by
    rw [show ((5949 / 3200) : ℝ) = ((3200 / 5949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (489859687 / 250000000) ≤ -Real.log (451 / 3200) ∧
    -Real.log (451 / 3200) ≤ (1959438751 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 1251)) (n := 12)
    (lo := (143286097 / 250000000)) (hi := (573144389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 451) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 451) = 1/(451 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1959438751 / 1000000000) (-489859687 / 250000000) (Real.log (451 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (123854711 / 200000000) ≤ -Real.log (12800 / 23777) ∧
    -Real.log (12800 / 23777) ≤ (154818389 / 250000000) := by
  have h := checkLog_sound (w := (10977 / 36577)) (n := 12)
    (lo := (123854711 / 200000000)) (hi := (154818389 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23777 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23777 / 12800) = 1/(12800 / 23777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (123854711 / 200000000) (154818389 / 250000000) (Real.log (23777 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23777 / 12800) = -Real.log (12800 / 23777) := by
    rw [show ((23777 / 12800) : ℝ) = ((12800 / 23777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (974480837 / 500000000) ≤ -Real.log (1823 / 12800) ∧
    -Real.log (1823 / 12800) ≤ (1948961677 / 1000000000) := by
  have h := checkLog_sound (w := (1377 / 5023)) (n := 12)
    (lo := (281333657 / 500000000)) (hi := (112533463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1823) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1823) = 1/(1823 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1948961677 / 1000000000) (-974480837 / 500000000) (Real.log (1823 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (132911163 / 200000000) ≤ -Real.log (1000000 / 1943627) ∧
    -Real.log (1000000 / 1943627) ≤ (83069477 / 125000000) := by
  have h := checkLog_sound (w := (943627 / 2943627)) (n := 12)
    (lo := (132911163 / 200000000)) (hi := (83069477 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1943627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1943627 / 1000000) = 1/(1000000 / 1943627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (132911163 / 200000000) (83069477 / 125000000) (Real.log (1943627 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1943627 / 1000000) = -Real.log (1000000 / 1943627) := by
    rw [show ((1943627 / 1000000) : ℝ) = ((1000000 / 1943627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (718941239 / 250000000) ≤ -Real.log (56373 / 1000000) ∧
    -Real.log (56373 / 1000000) ≤ (2875764961 / 1000000000) := by
  have h := checkLog_sound (w := (6127 / 118873)) (n := 12)
    (lo := (25794059 / 250000000)) (hi := (103176237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56373) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 56373) = 1/(56373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2875764961 / 1000000000) (-718941239 / 250000000) (Real.log (56373 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (664833607 / 1000000000) ≤ -Real.log (1000000 / 1944167) ∧
    -Real.log (1000000 / 1944167) ≤ (83104201 / 125000000) := by
  have h := checkLog_sound (w := (944167 / 2944167)) (n := 12)
    (lo := (664833607 / 1000000000)) (hi := (83104201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1944167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1944167 / 1000000) = 1/(1000000 / 1944167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (664833607 / 1000000000) (83104201 / 125000000) (Real.log (1944167 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1944167 / 1000000) = -Real.log (1000000 / 1944167) := by
    rw [show ((1944167 / 1000000) : ℝ) = ((1000000 / 1944167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (360673773 / 125000000) ≤ -Real.log (55833 / 1000000) ∧
    -Real.log (55833 / 1000000) ≤ (2885390189 / 1000000000) := by
  have h := checkLog_sound (w := (6667 / 118333)) (n := 12)
    (lo := (14100183 / 125000000)) (hi := (22560293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55833) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 55833) = 1/(55833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2885390189 / 1000000000) (-360673773 / 125000000) (Real.log (55833 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (166000257 / 250000000) ≤ -Real.log (1000000 / 1942549) ∧
    -Real.log (1000000 / 1942549) ≤ (664001029 / 1000000000) := by
  have h := checkLog_sound (w := (942549 / 2942549)) (n := 12)
    (lo := (166000257 / 250000000)) (hi := (664001029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1942549 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1942549 / 1000000) = 1/(1000000 / 1942549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (166000257 / 250000000) (664001029 / 1000000000) (Real.log (1942549 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1942549 / 1000000) = -Real.log (1000000 / 1942549) := by
    rw [show ((1942549 / 1000000) : ℝ) = ((1000000 / 1942549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1428411433 / 500000000) ≤ -Real.log (57451 / 1000000) ∧
    -Real.log (57451 / 1000000) ≤ (2856822871 / 1000000000) := by
  have h := checkLog_sound (w := (5049 / 119951)) (n := 12)
    (lo := (42117073 / 500000000)) (hi := (84234147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57451) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 57451) = 1/(57451 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2856822871 / 1000000000) (-1428411433 / 500000000) (Real.log (57451 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (132858471 / 200000000) ≤ -Real.log (200000 / 388623) ∧
    -Real.log (200000 / 388623) ≤ (166073089 / 250000000) := by
  have h := checkLog_sound (w := (188623 / 588623)) (n := 12)
    (lo := (132858471 / 200000000)) (hi := (166073089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388623 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388623 / 200000) = 1/(200000 / 388623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (132858471 / 200000000) (166073089 / 250000000) (Real.log (388623 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (388623 / 200000) = -Real.log (200000 / 388623) := by
    rw [show ((388623 / 200000) : ℝ) = ((200000 / 388623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (286672359 / 100000000) ≤ -Real.log (11377 / 200000) ∧
    -Real.log (11377 / 200000) ≤ (573344719 / 200000000) := by
  have h := checkLog_sound (w := (1123 / 23877)) (n := 12)
    (lo := (9413487 / 100000000)) (hi := (94134871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11377) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 11377) = 1/(11377 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-573344719 / 200000000) (-286672359 / 100000000) (Real.log (11377 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (354032077 / 100000000) ≤ -Real.log (250000000000 / 8619494261437) ∧
    -Real.log (250000000000 / 8619494261437) ≤ (442540097 / 125000000) := by
  have h := checkLog_sound (w := (619494261437 / 16619494261437)) (n := 12)
    (lo := (7458487 / 100000000)) (hi := (74584871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8619494261437 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(8619494261437 / 8000000000000) = 1/(250000000000 / 8619494261437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (354032077 / 100000000) (442540097 / 125000000) (Real.log (8619494261437 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8619494261437 / 250000000000) = -Real.log (250000000000 / 8619494261437) := by
    rw [show ((8619494261437 / 250000000000) : ℝ) = ((250000000000 / 8619494261437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3550223791 / 1000000000) ≤ -Real.log (500000000000 / 17410554689879) ∧
    -Real.log (500000000000 / 17410554689879) ≤ (3550223797 / 1000000000) := by
  have h := checkLog_sound (w := (1410554689879 / 33410554689879)) (n := 12)
    (lo := (84487891 / 1000000000)) (hi := (21121973 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17410554689879 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17410554689879 / 16000000000000) = 1/(500000000000 / 17410554689879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3550223791 / 1000000000) (3550223797 / 1000000000) (Real.log (17410554689879 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (17410554689879 / 500000000000) = -Real.log (500000000000 / 17410554689879) := by
    rw [show ((17410554689879 / 500000000000) : ℝ) = ((500000000000 / 17410554689879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3520823893 / 1000000000) ≤ -Real.log (31250000000 / 1056633587753) ∧
    -Real.log (31250000000 / 1056633587753) ≤ (3520823899 / 1000000000) := by
  have h := checkLog_sound (w := (56633587753 / 2056633587753)) (n := 12)
    (lo := (55087993 / 1000000000)) (hi := (27543997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1056633587753 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1056633587753 / 1000000000000) = 1/(31250000000 / 1056633587753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3520823893 / 1000000000) (3520823899 / 1000000000) (Real.log (1056633587753 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1056633587753 / 31250000000) = -Real.log (31250000000 / 1056633587753) := by
    rw [show ((1056633587753 / 31250000000) : ℝ) = ((31250000000 / 1056633587753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (706203189 / 200000000) ≤ -Real.log (500000000000 / 17079326711787) ∧
    -Real.log (500000000000 / 17079326711787) ≤ (3531015951 / 1000000000) := by
  have h := checkLog_sound (w := (1079326711787 / 33079326711787)) (n := 12)
    (lo := (13056009 / 200000000)) (hi := (32640023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17079326711787 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17079326711787 / 16000000000000) = 1/(500000000000 / 17079326711787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (706203189 / 200000000) (3531015951 / 1000000000) (Real.log (17079326711787 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (17079326711787 / 500000000000) = -Real.log (500000000000 / 17079326711787) := by
    rw [show ((17079326711787 / 500000000000) : ℝ) = ((500000000000 / 17079326711787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0143
