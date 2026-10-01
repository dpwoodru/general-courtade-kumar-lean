import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell197
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (311898199 / 1000000000) ≤ -Real.log (2560 / 3497) ∧
    -Real.log (2560 / 3497) ≤ (1559491 / 5000000) := by
  have h := checkLog_sound (w := (937 / 6057)) (n := 12)
    (lo := (311898199 / 1000000000)) (hi := (1559491 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3497 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3497 / 2560) = 1/(2560 / 3497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (311898199 / 1000000000) (1559491 / 5000000) (Real.log (3497 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3497 / 2560) = -Real.log (2560 / 3497) := by
    rw [show ((3497 / 2560) : ℝ) = ((2560 / 3497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (455730969 / 1000000000) ≤ -Real.log (1623 / 2560) ∧
    -Real.log (1623 / 2560) ≤ (45573097 / 100000000) := by
  have h := checkLog_sound (w := (937 / 4183)) (n := 12)
    (lo := (455730969 / 1000000000)) (hi := (45573097 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1623) = 1/(1623 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-45573097 / 100000000) (-455730969 / 1000000000) (Real.log (1623 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (19466823 / 62500000) ≤ -Real.log (5120 / 6991) ∧
    -Real.log (5120 / 6991) ≤ (311469169 / 1000000000) := by
  have h := checkLog_sound (w := (1871 / 12111)) (n := 12)
    (lo := (19466823 / 62500000)) (hi := (311469169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6991 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6991 / 5120) = 1/(5120 / 6991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (19466823 / 62500000) (311469169 / 1000000000) (Real.log (6991 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6991 / 5120) = -Real.log (5120 / 6991) := by
    rw [show ((6991 / 5120) : ℝ) = ((5120 / 6991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (227403591 / 500000000) ≤ -Real.log (3249 / 5120) ∧
    -Real.log (3249 / 5120) ≤ (454807183 / 1000000000) := by
  have h := checkLog_sound (w := (1871 / 8369)) (n := 12)
    (lo := (227403591 / 500000000)) (hi := (454807183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3249) = 1/(3249 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-454807183 / 1000000000) (-227403591 / 500000000) (Real.log (3249 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (11552451 / 50000000) ≤ -Real.log (1000000 / 1259921) ∧
    -Real.log (1000000 / 1259921) ≤ (231049021 / 1000000000) := by
  have h := checkLog_sound (w := (259921 / 2259921)) (n := 12)
    (lo := (11552451 / 50000000)) (hi := (231049021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259921 / 1000000) = 1/(1000000 / 1259921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (11552451 / 50000000) (231049021 / 1000000000) (Real.log (1259921 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1259921 / 1000000) = -Real.log (1000000 / 1259921) := by
    rw [show ((1259921 / 1000000) : ℝ) = ((1000000 / 1259921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (300998341 / 1000000000) ≤ -Real.log (740079 / 1000000) ∧
    -Real.log (740079 / 1000000) ≤ (150499171 / 500000000) := by
  have h := checkLog_sound (w := (259921 / 1740079)) (n := 12)
    (lo := (300998341 / 1000000000)) (hi := (150499171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 740079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 740079) = 1/(740079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-150499171 / 500000000) (-300998341 / 1000000000) (Real.log (740079 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (231384699 / 1000000000) ≤ -Real.log (125000 / 157543) ∧
    -Real.log (125000 / 157543) ≤ (2313847 / 10000000) := by
  have h := checkLog_sound (w := (32543 / 282543)) (n := 12)
    (lo := (231384699 / 1000000000)) (hi := (2313847 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157543 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157543 / 125000) = 1/(125000 / 157543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (231384699 / 1000000000) (2313847 / 10000000) (Real.log (157543 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (157543 / 125000) = -Real.log (125000 / 157543) := by
    rw [show ((157543 / 125000) : ℝ) = ((125000 / 157543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (60314013 / 200000000) ≤ -Real.log (92457 / 125000) ∧
    -Real.log (92457 / 125000) ≤ (150785033 / 500000000) := by
  have h := checkLog_sound (w := (32543 / 217457)) (n := 12)
    (lo := (60314013 / 200000000)) (hi := (150785033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 92457) = 1/(92457 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-150785033 / 500000000) (-60314013 / 200000000) (Real.log (92457 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (85839647 / 500000000) ≤ -Real.log (1000000 / 1187297) ∧
    -Real.log (1000000 / 1187297) ≤ (34335859 / 200000000) := by
  have h := checkLog_sound (w := (187297 / 2187297)) (n := 12)
    (lo := (85839647 / 500000000)) (hi := (34335859 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187297 / 1000000) = 1/(1000000 / 1187297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (85839647 / 500000000) (34335859 / 200000000) (Real.log (1187297 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1187297 / 1000000) = -Real.log (1000000 / 1187297) := by
    rw [show ((1187297 / 1000000) : ℝ) = ((1000000 / 1187297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (207389549 / 1000000000) ≤ -Real.log (812703 / 1000000) ∧
    -Real.log (812703 / 1000000) ≤ (4147791 / 20000000) := by
  have h := checkLog_sound (w := (187297 / 1812703)) (n := 12)
    (lo := (207389549 / 1000000000)) (hi := (4147791 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 812703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 812703) = 1/(812703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4147791 / 20000000) (-207389549 / 1000000000) (Real.log (812703 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17194541 / 100000000) ≤ -Real.log (1000000 / 1187613) ∧
    -Real.log (1000000 / 1187613) ≤ (171945411 / 1000000000) := by
  have h := checkLog_sound (w := (187613 / 2187613)) (n := 12)
    (lo := (17194541 / 100000000)) (hi := (171945411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187613 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187613 / 1000000) = 1/(1000000 / 1187613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17194541 / 100000000) (171945411 / 1000000000) (Real.log (1187613 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1187613 / 1000000) = -Real.log (1000000 / 1187613) := by
    rw [show ((1187613 / 1000000) : ℝ) = ((1000000 / 1187613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (207778451 / 1000000000) ≤ -Real.log (812387 / 1000000) ∧
    -Real.log (812387 / 1000000) ≤ (51944613 / 250000000) := by
  have h := checkLog_sound (w := (187613 / 1812387)) (n := 12)
    (lo := (207778451 / 1000000000)) (hi := (51944613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 812387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 812387) = 1/(812387 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-51944613 / 250000000) (-207778451 / 1000000000) (Real.log (812387 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (15325527 / 20000000) ≤ -Real.log (500000000000 / 1075869498307) ∧
    -Real.log (500000000000 / 1075869498307) ≤ (2993267 / 3906250) := by
  have h := checkLog_sound (w := (75869498307 / 2075869498307)) (n := 12)
    (lo := (7312917 / 100000000)) (hi := (73129171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075869498307 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1075869498307 / 1000000000000) = 1/(500000000000 / 1075869498307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (15325527 / 20000000) (2993267 / 3906250) (Real.log (1075869498307 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1075869498307 / 500000000000) = -Real.log (500000000000 / 1075869498307) := by
    rw [show ((1075869498307 / 500000000000) : ℝ) = ((500000000000 / 1075869498307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (47976823 / 62500000) ≤ -Real.log (250000000000 / 538662969809) ∧
    -Real.log (250000000000 / 538662969809) ≤ (76762917 / 100000000) := by
  have h := checkLog_sound (w := (38662969809 / 1038662969809)) (n := 12)
    (lo := (18620497 / 250000000)) (hi := (74481989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538662969809 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(538662969809 / 500000000000) = 1/(250000000000 / 538662969809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (47976823 / 62500000) (76762917 / 100000000) (Real.log (538662969809 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (538662969809 / 250000000000) = -Real.log (250000000000 / 538662969809) := by
    rw [show ((538662969809 / 250000000000) : ℝ) = ((250000000000 / 538662969809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (266023681 / 500000000) ≤ -Real.log (500000000000 / 851207100863) ∧
    -Real.log (500000000000 / 851207100863) ≤ (532047363 / 1000000000) := by
  have h := checkLog_sound (w := (351207100863 / 1351207100863)) (n := 12)
    (lo := (266023681 / 500000000)) (hi := (532047363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851207100863 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851207100863 / 500000000000) = 1/(500000000000 / 851207100863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (266023681 / 500000000) (532047363 / 1000000000) (Real.log (851207100863 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (851207100863 / 500000000000) = -Real.log (500000000000 / 851207100863) := by
    rw [show ((851207100863 / 500000000000) : ℝ) = ((500000000000 / 851207100863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (106590953 / 200000000) ≤ -Real.log (500000000000 / 851979839277) ∧
    -Real.log (500000000000 / 851979839277) ≤ (266477383 / 500000000) := by
  have h := checkLog_sound (w := (351979839277 / 1351979839277)) (n := 12)
    (lo := (106590953 / 200000000)) (hi := (266477383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851979839277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851979839277 / 500000000000) = 1/(500000000000 / 851979839277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (106590953 / 200000000) (266477383 / 500000000) (Real.log (851979839277 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (851979839277 / 500000000000) = -Real.log (500000000000 / 851979839277) := by
    rw [show ((851979839277 / 500000000000) : ℝ) = ((500000000000 / 851979839277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (94767211 / 250000000) ≤ -Real.log (500000000000 / 730461804619) ∧
    -Real.log (500000000000 / 730461804619) ≤ (75813769 / 200000000) := by
  have h := checkLog_sound (w := (230461804619 / 1230461804619)) (n := 12)
    (lo := (94767211 / 250000000)) (hi := (75813769 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730461804619 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730461804619 / 500000000000) = 1/(500000000000 / 730461804619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (94767211 / 250000000) (75813769 / 200000000) (Real.log (730461804619 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (730461804619 / 500000000000) = -Real.log (500000000000 / 730461804619) := by
    rw [show ((730461804619 / 500000000000) : ℝ) = ((500000000000 / 730461804619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (379723861 / 1000000000) ≤ -Real.log (500000000000 / 730940426177) ∧
    -Real.log (500000000000 / 730940426177) ≤ (189861931 / 500000000) := by
  have h := checkLog_sound (w := (230940426177 / 1230940426177)) (n := 12)
    (lo := (379723861 / 1000000000)) (hi := (189861931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730940426177 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730940426177 / 500000000000) = 1/(500000000000 / 730940426177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (379723861 / 1000000000) (189861931 / 500000000) (Real.log (730940426177 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (730940426177 / 500000000000) = -Real.log (500000000000 / 730940426177) := by
    rw [show ((730940426177 / 500000000000) : ℝ) = ((500000000000 / 730940426177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (35833041 / 1000000000) ≤ -Real.log (964801362231 / 1000000000000) ∧
    -Real.log (964801362231 / 1000000000000) ≤ (17916521 / 500000000) := by
  have h := checkLog_sound (w := (35198637769 / 1964801362231)) (n := 12)
    (lo := (35833041 / 1000000000)) (hi := (17916521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964801362231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964801362231) = 1/(964801362231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17916521 / 500000000) (-35833041 / 1000000000) (Real.log (964801362231 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (17855127 / 500000000) ≤ -Real.log (964919833791 / 1000000000000) ∧
    -Real.log (964919833791 / 1000000000000) ≤ (7142051 / 200000000) := by
  have h := checkLog_sound (w := (35080166209 / 1964919833791)) (n := 12)
    (lo := (17855127 / 500000000)) (hi := (7142051 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964919833791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964919833791) = 1/(964919833791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-7142051 / 200000000) (-17855127 / 500000000) (Real.log (964919833791 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell197
