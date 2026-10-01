import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0148
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

theorem reflection_log_1_neg : (654966551 / 1000000000) ≤ -Real.log (12800 / 24641) ∧
    -Real.log (12800 / 24641) ≤ (81870819 / 125000000) := by
  have h := checkLog_sound (w := (11841 / 37441)) (n := 12)
    (lo := (654966551 / 1000000000)) (hi := (81870819 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24641 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24641 / 12800) = 1/(12800 / 24641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (654966551 / 1000000000) (81870819 / 125000000) (Real.log (24641 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24641 / 12800) = -Real.log (12800 / 24641) := by
    rw [show ((24641 / 12800) : ℝ) = ((12800 / 24641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2591309373 / 1000000000) ≤ -Real.log (959 / 12800) ∧
    -Real.log (959 / 12800) ≤ (2591309377 / 1000000000) := by
  have h := checkLog_sound (w := (641 / 2559)) (n := 12)
    (lo := (511867833 / 1000000000)) (hi := (255933917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 959) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 959) = 1/(959 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2591309377 / 1000000000) (-2591309373 / 1000000000) (Real.log (959 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (654195181 / 1000000000) ≤ -Real.log (6400 / 12311) ∧
    -Real.log (6400 / 12311) ≤ (327097591 / 500000000) := by
  have h := checkLog_sound (w := (5911 / 18711)) (n := 12)
    (lo := (654195181 / 1000000000)) (hi := (327097591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12311 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12311 / 6400) = 1/(6400 / 12311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (654195181 / 1000000000) (327097591 / 500000000) (Real.log (12311 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12311 / 6400) = -Real.log (6400 / 12311) := by
    rw [show ((12311 / 6400) : ℝ) = ((6400 / 12311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1285845389 / 500000000) ≤ -Real.log (489 / 6400) ∧
    -Real.log (489 / 6400) ≤ (1285845391 / 500000000) := by
  have h := checkLog_sound (w := (311 / 1289)) (n := 12)
    (lo := (246124619 / 500000000)) (hi := (492249239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 489) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 489) = 1/(489 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1285845391 / 500000000) (-1285845389 / 500000000) (Real.log (489 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (307635047 / 500000000) ≤ -Real.log (6400 / 11841) ∧
    -Real.log (6400 / 11841) ≤ (123054019 / 200000000) := by
  have h := checkLog_sound (w := (5441 / 18241)) (n := 12)
    (lo := (307635047 / 500000000)) (hi := (123054019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11841 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11841 / 6400) = 1/(6400 / 11841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (307635047 / 500000000) (123054019 / 200000000) (Real.log (11841 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11841 / 6400) = -Real.log (6400 / 11841) := by
    rw [show ((11841 / 6400) : ℝ) = ((6400 / 11841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1898162193 / 1000000000) ≤ -Real.log (959 / 6400) ∧
    -Real.log (959 / 6400) ≤ (474540549 / 250000000) := by
  have h := checkLog_sound (w := (641 / 2559)) (n := 12)
    (lo := (511867833 / 1000000000)) (hi := (255933917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 959) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 959) = 1/(959 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-474540549 / 250000000) (-1898162193 / 1000000000) (Real.log (959 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (153416053 / 250000000) ≤ -Real.log (3200 / 5911) ∧
    -Real.log (3200 / 5911) ≤ (613664213 / 1000000000) := by
  have h := checkLog_sound (w := (2711 / 9111)) (n := 12)
    (lo := (153416053 / 250000000)) (hi := (613664213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5911 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5911 / 3200) = 1/(3200 / 5911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (153416053 / 250000000) (613664213 / 1000000000) (Real.log (5911 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5911 / 3200) = -Real.log (3200 / 5911) := by
    rw [show ((5911 / 3200) : ℝ) = ((3200 / 5911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (939271799 / 500000000) ≤ -Real.log (489 / 3200) ∧
    -Real.log (489 / 3200) ≤ (1878543601 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 1289)) (n := 12)
    (lo := (246124619 / 500000000)) (hi := (492249239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 489) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 489) = 1/(489 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1878543601 / 1000000000) (-939271799 / 500000000) (Real.log (489 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (662625599 / 1000000000) ≤ -Real.log (1000000 / 1939879) ∧
    -Real.log (1000000 / 1939879) ≤ (414141 / 625000) := by
  have h := checkLog_sound (w := (939879 / 2939879)) (n := 12)
    (lo := (662625599 / 1000000000)) (hi := (414141 / 625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1939879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1939879 / 1000000) = 1/(1000000 / 1939879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (662625599 / 1000000000) (414141 / 625000) (Real.log (1939879 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1939879 / 1000000) = -Real.log (1000000 / 1939879) := by
    rw [show ((1939879 / 1000000) : ℝ) = ((1000000 / 1939879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1405698039 / 500000000) ≤ -Real.log (60121 / 1000000) ∧
    -Real.log (60121 / 1000000) ≤ (2811396083 / 1000000000) := by
  have h := checkLog_sound (w := (2379 / 122621)) (n := 12)
    (lo := (19403679 / 500000000)) (hi := (38807359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 60121) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 60121) = 1/(60121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2811396083 / 1000000000) (-1405698039 / 500000000) (Real.log (60121 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (331587999 / 500000000) ≤ -Real.log (1000000 / 1940947) ∧
    -Real.log (1000000 / 1940947) ≤ (663175999 / 1000000000) := by
  have h := checkLog_sound (w := (940947 / 2940947)) (n := 12)
    (lo := (331587999 / 500000000)) (hi := (663175999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1940947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1940947 / 1000000) = 1/(1000000 / 1940947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (331587999 / 500000000) (663175999 / 1000000000) (Real.log (1940947 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1940947 / 1000000) = -Real.log (1000000 / 1940947) := by
    rw [show ((1940947 / 1000000) : ℝ) = ((1000000 / 1940947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (282931993 / 100000000) ≤ -Real.log (59053 / 1000000) ∧
    -Real.log (59053 / 1000000) ≤ (565863987 / 200000000) := by
  have h := checkLog_sound (w := (3447 / 121553)) (n := 12)
    (lo := (5673121 / 100000000)) (hi := (56731211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 59053) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 59053) = 1/(59053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-565863987 / 200000000) (-282931993 / 100000000) (Real.log (59053 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (661972253 / 1000000000) ≤ -Real.log (250000 / 484653) ∧
    -Real.log (250000 / 484653) ≤ (330986127 / 500000000) := by
  have h := checkLog_sound (w := (234653 / 734653)) (n := 12)
    (lo := (661972253 / 1000000000)) (hi := (330986127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484653 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(484653 / 250000) = 1/(250000 / 484653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (661972253 / 1000000000) (330986127 / 500000000) (Real.log (484653 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (484653 / 250000) = -Real.log (250000 / 484653) := by
    rw [show ((484653 / 250000) : ℝ) = ((250000 / 484653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (27905409 / 10000000) ≤ -Real.log (15347 / 250000) ∧
    -Real.log (15347 / 250000) ≤ (558108181 / 200000000) := by
  have h := checkLog_sound (w := (139 / 15486)) (n := 12)
    (lo := (897609 / 50000000)) (hi := (17952181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15347) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 15347) = 1/(15347 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-558108181 / 200000000) (-27905409 / 10000000) (Real.log (15347 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (132510273 / 200000000) ≤ -Real.log (200000 / 387947) ∧
    -Real.log (200000 / 387947) ≤ (331275683 / 500000000) := by
  have h := checkLog_sound (w := (187947 / 587947)) (n := 12)
    (lo := (132510273 / 200000000)) (hi := (331275683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387947 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387947 / 200000) = 1/(200000 / 387947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (132510273 / 200000000) (331275683 / 500000000) (Real.log (387947 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (387947 / 200000) = -Real.log (200000 / 387947) := by
    rw [show ((387947 / 200000) : ℝ) = ((200000 / 387947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (702250943 / 250000000) ≤ -Real.log (12053 / 200000) ∧
    -Real.log (12053 / 200000) ≤ (2809003777 / 1000000000) := by
  have h := checkLog_sound (w := (447 / 24553)) (n := 12)
    (lo := (9103763 / 250000000)) (hi := (36415053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 12053) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 12053) = 1/(12053 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2809003777 / 1000000000) (-702250943 / 250000000) (Real.log (12053 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1737010839 / 500000000) ≤ -Real.log (500000000000 / 16133123201543) ∧
    -Real.log (500000000000 / 16133123201543) ≤ (868505421 / 250000000) := by
  have h := checkLog_sound (w := (133123201543 / 32133123201543)) (n := 12)
    (lo := (4142889 / 500000000)) (hi := (8285779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16133123201543 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16133123201543 / 16000000000000) = 1/(500000000000 / 16133123201543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1737010839 / 500000000) (868505421 / 250000000) (Real.log (16133123201543 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (16133123201543 / 500000000000) = -Real.log (500000000000 / 16133123201543) := by
    rw [show ((16133123201543 / 500000000000) : ℝ) = ((500000000000 / 16133123201543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (436561991 / 125000000) ≤ -Real.log (25000000000 / 821697034867) ∧
    -Real.log (25000000000 / 821697034867) ≤ (1746247967 / 500000000) := by
  have h := checkLog_sound (w := (21697034867 / 1621697034867)) (n := 12)
    (lo := (6690007 / 250000000)) (hi := (26760029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821697034867 / 800000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(821697034867 / 800000000000) = 1/(25000000000 / 821697034867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (436561991 / 125000000) (1746247967 / 500000000) (Real.log (821697034867 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (821697034867 / 25000000000) = -Real.log (25000000000 / 821697034867) := by
    rw [show ((821697034867 / 25000000000) : ℝ) = ((25000000000 / 821697034867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3452513153 / 1000000000) ≤ -Real.log (250000000000 / 7894914315501) ∧
    -Real.log (250000000000 / 7894914315501) ≤ (1726256579 / 500000000) := by
  have h := checkLog_sound (w := (3894914315501 / 11894914315501)) (n := 12)
    (lo := (679924433 / 1000000000)) (hi := (339962217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7894914315501 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7894914315501 / 4000000000000) = 1/(250000000000 / 7894914315501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3452513153 / 1000000000) (1726256579 / 500000000) (Real.log (7894914315501 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7894914315501 / 250000000000) = -Real.log (250000000000 / 7894914315501) := by
    rw [show ((7894914315501 / 250000000000) : ℝ) = ((250000000000 / 7894914315501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3471555137 / 1000000000) ≤ -Real.log (500000000000 / 16093379241683) ∧
    -Real.log (500000000000 / 16093379241683) ≤ (3471555143 / 1000000000) := by
  have h := checkLog_sound (w := (93379241683 / 32093379241683)) (n := 12)
    (lo := (5819237 / 1000000000)) (hi := (2909619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16093379241683 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16093379241683 / 16000000000000) = 1/(500000000000 / 16093379241683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3471555137 / 1000000000) (3471555143 / 1000000000) (Real.log (16093379241683 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (16093379241683 / 500000000000) = -Real.log (500000000000 / 16093379241683) := by
    rw [show ((16093379241683 / 500000000000) : ℝ) = ((500000000000 / 16093379241683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0148
