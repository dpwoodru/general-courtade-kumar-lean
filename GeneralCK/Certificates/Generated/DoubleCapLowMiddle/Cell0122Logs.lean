import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0122
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

theorem reflection_log_1_neg : (26612889 / 40000000) ≤ -Real.log (5120 / 9959) ∧
    -Real.log (5120 / 9959) ≤ (332661113 / 500000000) := by
  have h := checkLog_sound (w := (4839 / 15079)) (n := 12)
    (lo := (26612889 / 40000000)) (hi := (332661113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9959 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9959 / 5120) = 1/(5120 / 9959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (26612889 / 40000000) (332661113 / 500000000) (Real.log (9959 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (9959 / 5120) = -Real.log (5120 / 9959) := by
    rw [show ((9959 / 5120) : ℝ) = ((5120 / 9959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1451277523 / 500000000) ≤ -Real.log (281 / 5120) ∧
    -Real.log (281 / 5120) ≤ (2902555051 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 601)) (n := 12)
    (lo := (64983163 / 500000000)) (hi := (129966327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 281) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 281) = 1/(281 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2902555051 / 1000000000) (-1451277523 / 500000000) (Real.log (281 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (166235147 / 250000000) ≤ -Real.log (1600 / 3111) ∧
    -Real.log (1600 / 3111) ≤ (664940589 / 1000000000) := by
  have h := checkLog_sound (w := (1511 / 4711)) (n := 12)
    (lo := (166235147 / 250000000)) (hi := (664940589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3111 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3111 / 1600) = 1/(1600 / 3111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (166235147 / 250000000) (664940589 / 1000000000) (Real.log (3111 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3111 / 1600) = -Real.log (1600 / 3111) := by
    rw [show ((3111 / 1600) : ℝ) = ((1600 / 3111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (361140317 / 125000000) ≤ -Real.log (89 / 1600) ∧
    -Real.log (89 / 1600) ≤ (2889122541 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 189)) (n := 12)
    (lo := (14566727 / 125000000)) (hi := (116533817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 89) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(100 / 89) = 1/(89 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2889122541 / 1000000000) (-361140317 / 125000000) (Real.log (89 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (636700829 / 1000000000) ≤ -Real.log (2560 / 4839) ∧
    -Real.log (2560 / 4839) ≤ (63670083 / 100000000) := by
  have h := checkLog_sound (w := (2279 / 7399)) (n := 12)
    (lo := (636700829 / 1000000000)) (hi := (63670083 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4839 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4839 / 2560) = 1/(2560 / 4839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (636700829 / 1000000000) (63670083 / 100000000) (Real.log (4839 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4839 / 2560) = -Real.log (2560 / 4839) := by
    rw [show ((4839 / 2560) : ℝ) = ((2560 / 4839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1104703933 / 500000000) ≤ -Real.log (281 / 2560) ∧
    -Real.log (281 / 2560) ≤ (220940787 / 100000000) := by
  have h := checkLog_sound (w := (39 / 601)) (n := 12)
    (lo := (64983163 / 500000000)) (hi := (129966327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 281) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 281) = 1/(281 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-220940787 / 100000000) (-1104703933 / 500000000) (Real.log (281 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (317957617 / 500000000) ≤ -Real.log (800 / 1511) ∧
    -Real.log (800 / 1511) ≤ (127183047 / 200000000) := by
  have h := checkLog_sound (w := (711 / 2311)) (n := 12)
    (lo := (317957617 / 500000000)) (hi := (127183047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1511 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1511 / 800) = 1/(800 / 1511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (317957617 / 500000000) (127183047 / 200000000) (Real.log (1511 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1511 / 800) = -Real.log (800 / 1511) := by
    rw [show ((1511 / 800) : ℝ) = ((800 / 1511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (548993839 / 250000000) ≤ -Real.log (89 / 800) ∧
    -Real.log (89 / 800) ≤ (6862423 / 3125000) := by
  have h := checkLog_sound (w := (11 / 189)) (n := 12)
    (lo := (14566727 / 125000000)) (hi := (116533817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 89) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(100 / 89) = 1/(89 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-6862423 / 3125000) (-548993839 / 250000000) (Real.log (89 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67045413 / 100000000) ≤ -Real.log (8000 / 15641) ∧
    -Real.log (8000 / 15641) ≤ (670454131 / 1000000000) := by
  have h := checkLog_sound (w := (7641 / 23641)) (n := 12)
    (lo := (67045413 / 100000000)) (hi := (670454131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15641 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15641 / 8000) = 1/(8000 / 15641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67045413 / 100000000) (670454131 / 1000000000) (Real.log (15641 / 8000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (15641 / 8000) = -Real.log (8000 / 15641) := by
    rw [show ((15641 / 8000) : ℝ) = ((8000 / 15641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3103874429 / 1000000000) ≤ -Real.log (359 / 8000) ∧
    -Real.log (359 / 8000) ≤ (1551937217 / 500000000) := by
  have h := checkLog_sound (w := (141 / 859)) (n := 12)
    (lo := (331285709 / 1000000000)) (hi := (33128571 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 359) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(500 / 359) = 1/(359 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1551937217 / 500000000) (-3103874429 / 1000000000) (Real.log (359 / 8000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (167685001 / 250000000) ≤ -Real.log (250000 / 488921) ∧
    -Real.log (250000 / 488921) ≤ (134148001 / 200000000) := by
  have h := checkLog_sound (w := (238921 / 738921)) (n := 12)
    (lo := (167685001 / 250000000)) (hi := (134148001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((488921 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(488921 / 250000) = 1/(250000 / 488921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (167685001 / 250000000) (134148001 / 200000000) (Real.log (488921 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (488921 / 250000) = -Real.log (250000 / 488921) := by
    rw [show ((488921 / 250000) : ℝ) = ((250000 / 488921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3116409491 / 1000000000) ≤ -Real.log (11079 / 250000) ∧
    -Real.log (11079 / 250000) ≤ (389551187 / 125000000) := by
  have h := checkLog_sound (w := (2273 / 13352)) (n := 12)
    (lo := (343820771 / 1000000000)) (hi := (85955193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11079) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 11079) = 1/(11079 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-389551187 / 125000000) (-3116409491 / 1000000000) (Real.log (11079 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (670141057 / 1000000000) ≤ -Real.log (1000000 / 1954513) ∧
    -Real.log (1000000 / 1954513) ≤ (335070529 / 500000000) := by
  have h := checkLog_sound (w := (954513 / 2954513)) (n := 12)
    (lo := (670141057 / 1000000000)) (hi := (335070529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1954513 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1954513 / 1000000) = 1/(1000000 / 1954513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (670141057 / 1000000000) (335070529 / 500000000) (Real.log (1954513 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1954513 / 1000000) = -Real.log (1000000 / 1954513) := by
    rw [show ((1954513 / 1000000) : ℝ) = ((1000000 / 1954513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (618065741 / 200000000) ≤ -Real.log (45487 / 1000000) ∧
    -Real.log (45487 / 1000000) ≤ (309032871 / 100000000) := by
  have h := checkLog_sound (w := (17013 / 107987)) (n := 12)
    (lo := (63547997 / 200000000)) (hi := (158869993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45487) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 45487) = 1/(45487 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-309032871 / 100000000) (-618065741 / 200000000) (Real.log (45487 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (167609057 / 250000000) ≤ -Real.log (100000 / 195509) ∧
    -Real.log (100000 / 195509) ≤ (670436229 / 1000000000) := by
  have h := checkLog_sound (w := (95509 / 295509)) (n := 12)
    (lo := (167609057 / 250000000)) (hi := (670436229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195509 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195509 / 100000) = 1/(100000 / 195509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (167609057 / 250000000) (670436229 / 1000000000) (Real.log (195509 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (195509 / 100000) = -Real.log (100000 / 195509) := by
    rw [show ((195509 / 100000) : ℝ) = ((100000 / 195509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3103094789 / 1000000000) ≤ -Real.log (4491 / 100000) ∧
    -Real.log (4491 / 100000) ≤ (1551547397 / 500000000) := by
  have h := checkLog_sound (w := (1759 / 10741)) (n := 12)
    (lo := (330506069 / 1000000000)) (hi := (33050607 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4491) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 4491) = 1/(4491 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1551547397 / 500000000) (-3103094789 / 1000000000) (Real.log (4491 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3774328559 / 1000000000) ≤ -Real.log (250000000000 / 10892061281337) ∧
    -Real.log (250000000000 / 10892061281337) ≤ (754865713 / 200000000) := by
  have h := checkLog_sound (w := (2892061281337 / 18892061281337)) (n := 12)
    (lo := (308592659 / 1000000000)) (hi := (15429633 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10892061281337 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10892061281337 / 8000000000000) = 1/(250000000000 / 10892061281337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3774328559 / 1000000000) (754865713 / 200000000) (Real.log (10892061281337 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10892061281337 / 250000000000) = -Real.log (250000000000 / 10892061281337) := by
    rw [show ((10892061281337 / 250000000000) : ℝ) = ((250000000000 / 10892061281337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1893574747 / 500000000) ≤ -Real.log (12500000000 / 551630336673) ∧
    -Real.log (12500000000 / 551630336673) ≤ (7574299 / 2000000) := by
  have h := checkLog_sound (w := (151630336673 / 951630336673)) (n := 12)
    (lo := (160706797 / 500000000)) (hi := (64282719 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((551630336673 / 400000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(551630336673 / 400000000000) = 1/(12500000000 / 551630336673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1893574747 / 500000000) (7574299 / 2000000) (Real.log (551630336673 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (551630336673 / 12500000000) = -Real.log (12500000000 / 551630336673) := by
    rw [show ((551630336673 / 12500000000) : ℝ) = ((12500000000 / 551630336673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1880234881 / 500000000) ≤ -Real.log (500000000000 / 21484303207509) ∧
    -Real.log (500000000000 / 21484303207509) ≤ (470058721 / 125000000) := by
  have h := checkLog_sound (w := (5484303207509 / 37484303207509)) (n := 12)
    (lo := (147366931 / 500000000)) (hi := (294733863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21484303207509 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(21484303207509 / 16000000000000) = 1/(500000000000 / 21484303207509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1880234881 / 500000000) (470058721 / 125000000) (Real.log (21484303207509 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (21484303207509 / 500000000000) = -Real.log (500000000000 / 21484303207509) := by
    rw [show ((21484303207509 / 500000000000) : ℝ) = ((500000000000 / 21484303207509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3773531017 / 1000000000) ≤ -Real.log (50000000000 / 2176675573369) ∧
    -Real.log (50000000000 / 2176675573369) ≤ (3773531023 / 1000000000) := by
  have h := checkLog_sound (w := (576675573369 / 3776675573369)) (n := 12)
    (lo := (307795117 / 1000000000)) (hi := (153897559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2176675573369 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2176675573369 / 1600000000000) = 1/(50000000000 / 2176675573369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3773531017 / 1000000000) (3773531023 / 1000000000) (Real.log (2176675573369 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2176675573369 / 50000000000) = -Real.log (50000000000 / 2176675573369) := by
    rw [show ((2176675573369 / 50000000000) : ℝ) = ((50000000000 / 2176675573369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0122
