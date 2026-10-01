import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0427
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

theorem reflection_log_1_neg : (12108177 / 62500000) ≤ -Real.log (10240 / 12429) ∧
    -Real.log (10240 / 12429) ≤ (193730833 / 1000000000) := by
  have h := checkLog_sound (w := (2189 / 22669)) (n := 12)
    (lo := (12108177 / 62500000)) (hi := (193730833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12429 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12429 / 10240) = 1/(10240 / 12429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12108177 / 62500000) (193730833 / 1000000000) (Real.log (12429 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12429 / 10240) = -Real.log (10240 / 12429) := by
    rw [show ((12429 / 10240) : ℝ) = ((10240 / 12429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (7515791 / 31250000) ≤ -Real.log (8051 / 10240) ∧
    -Real.log (8051 / 10240) ≤ (240505313 / 1000000000) := by
  have h := checkLog_sound (w := (2189 / 18291)) (n := 12)
    (lo := (7515791 / 31250000)) (hi := (240505313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8051) = 1/(8051 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-240505313 / 1000000000) (-7515791 / 31250000) (Real.log (8051 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (24186179 / 125000000) ≤ -Real.log (5120 / 6213) ∧
    -Real.log (5120 / 6213) ≤ (193489433 / 1000000000) := by
  have h := checkLog_sound (w := (1093 / 11333)) (n := 12)
    (lo := (24186179 / 125000000)) (hi := (193489433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6213 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6213 / 5120) = 1/(5120 / 6213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (24186179 / 125000000) (193489433 / 1000000000) (Real.log (6213 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6213 / 5120) = -Real.log (5120 / 6213) := by
    rw [show ((6213 / 5120) : ℝ) = ((5120 / 6213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (240132757 / 1000000000) ≤ -Real.log (4027 / 5120) ∧
    -Real.log (4027 / 5120) ≤ (120066379 / 500000000) := by
  have h := checkLog_sound (w := (1093 / 9147)) (n := 12)
    (lo := (240132757 / 1000000000)) (hi := (120066379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4027) = 1/(4027 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-120066379 / 500000000) (-240132757 / 1000000000) (Real.log (4027 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (177976013 / 500000000) ≤ -Real.log (5120 / 7309) ∧
    -Real.log (5120 / 7309) ≤ (355952027 / 1000000000) := by
  have h := checkLog_sound (w := (2189 / 12429)) (n := 12)
    (lo := (177976013 / 500000000)) (hi := (355952027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7309 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7309 / 5120) = 1/(5120 / 7309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (177976013 / 500000000) (355952027 / 1000000000) (Real.log (7309 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7309 / 5120) = -Real.log (5120 / 7309) := by
    rw [show ((7309 / 5120) : ℝ) = ((5120 / 7309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (557810777 / 1000000000) ≤ -Real.log (2931 / 5120) ∧
    -Real.log (2931 / 5120) ≤ (278905389 / 500000000) := by
  have h := checkLog_sound (w := (2189 / 8051)) (n := 12)
    (lo := (557810777 / 1000000000)) (hi := (278905389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2931) = 1/(2931 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-278905389 / 500000000) (-557810777 / 1000000000) (Real.log (2931 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (355541489 / 1000000000) ≤ -Real.log (2560 / 3653) ∧
    -Real.log (2560 / 3653) ≤ (35554149 / 100000000) := by
  have h := checkLog_sound (w := (1093 / 6213)) (n := 12)
    (lo := (355541489 / 1000000000)) (hi := (35554149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3653 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3653 / 2560) = 1/(2560 / 3653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (355541489 / 1000000000) (35554149 / 100000000) (Real.log (3653 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3653 / 2560) = -Real.log (2560 / 3653) := by
    rw [show ((3653 / 2560) : ℝ) = ((2560 / 3653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (556787759 / 1000000000) ≤ -Real.log (1467 / 2560) ∧
    -Real.log (1467 / 2560) ≤ (6959847 / 12500000) := by
  have h := checkLog_sound (w := (1093 / 4027)) (n := 12)
    (lo := (556787759 / 1000000000)) (hi := (6959847 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1467) = 1/(1467 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-6959847 / 12500000) (-556787759 / 1000000000) (Real.log (1467 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (265732431 / 1000000000) ≤ -Real.log (500000 / 652193) ∧
    -Real.log (500000 / 652193) ≤ (16608277 / 62500000) := by
  have h := checkLog_sound (w := (152193 / 1152193)) (n := 12)
    (lo := (265732431 / 1000000000)) (hi := (16608277 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((652193 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(652193 / 500000) = 1/(500000 / 652193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (265732431 / 1000000000) (16608277 / 62500000) (Real.log (652193 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (652193 / 500000) = -Real.log (500000 / 652193) := by
    rw [show ((652193 / 500000) : ℝ) = ((500000 / 652193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (36296037 / 100000000) ≤ -Real.log (347807 / 500000) ∧
    -Real.log (347807 / 500000) ≤ (362960371 / 1000000000) := by
  have h := checkLog_sound (w := (152193 / 847807)) (n := 12)
    (lo := (36296037 / 100000000)) (hi := (362960371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 347807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 347807) = 1/(347807 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-362960371 / 1000000000) (-36296037 / 100000000) (Real.log (347807 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (266058969 / 1000000000) ≤ -Real.log (250000 / 326203) ∧
    -Real.log (250000 / 326203) ≤ (26605897 / 100000000) := by
  have h := checkLog_sound (w := (76203 / 576203)) (n := 12)
    (lo := (266058969 / 1000000000)) (hi := (26605897 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326203 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326203 / 250000) = 1/(250000 / 326203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (266058969 / 1000000000) (26605897 / 100000000) (Real.log (326203 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (326203 / 250000) = -Real.log (250000 / 326203) := by
    rw [show ((326203 / 250000) : ℝ) = ((250000 / 326203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (181786483 / 500000000) ≤ -Real.log (173797 / 250000) ∧
    -Real.log (173797 / 250000) ≤ (363572967 / 1000000000) := by
  have h := checkLog_sound (w := (76203 / 423797)) (n := 12)
    (lo := (181786483 / 500000000)) (hi := (363572967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 173797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 173797) = 1/(173797 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-363572967 / 1000000000) (-181786483 / 500000000) (Real.log (173797 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (199588291 / 1000000000) ≤ -Real.log (10000 / 12209) ∧
    -Real.log (10000 / 12209) ≤ (49897073 / 250000000) := by
  have h := checkLog_sound (w := (2209 / 22209)) (n := 12)
    (lo := (199588291 / 1000000000)) (hi := (49897073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12209 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12209 / 10000) = 1/(10000 / 12209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (199588291 / 1000000000) (49897073 / 250000000) (Real.log (12209 / 10000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (12209 / 10000) = -Real.log (10000 / 12209) := by
    rw [show ((12209 / 10000) : ℝ) = ((10000 / 12209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (249615871 / 1000000000) ≤ -Real.log (7791 / 10000) ∧
    -Real.log (7791 / 10000) ≤ (487531 / 1953125) := by
  have h := checkLog_sound (w := (2209 / 17791)) (n := 12)
    (lo := (249615871 / 1000000000)) (hi := (487531 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 7791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 7791) = 1/(7791 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-487531 / 1953125) (-249615871 / 1000000000) (Real.log (7791 / 10000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (24981909 / 125000000) ≤ -Real.log (500000 / 610613) ∧
    -Real.log (500000 / 610613) ≤ (199855273 / 1000000000) := by
  have h := checkLog_sound (w := (110613 / 1110613)) (n := 12)
    (lo := (24981909 / 125000000)) (hi := (199855273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610613 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610613 / 500000) = 1/(500000 / 610613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (24981909 / 125000000) (199855273 / 1000000000) (Real.log (610613 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (610613 / 500000) = -Real.log (500000 / 610613) := by
    rw [show ((610613 / 500000) : ℝ) = ((500000 / 610613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (25003439 / 100000000) ≤ -Real.log (389387 / 500000) ∧
    -Real.log (389387 / 500000) ≤ (250034391 / 1000000000) := by
  have h := checkLog_sound (w := (110613 / 889387)) (n := 12)
    (lo := (25003439 / 100000000)) (hi := (250034391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 389387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 389387) = 1/(389387 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-250034391 / 1000000000) (-25003439 / 100000000) (Real.log (389387 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (314346401 / 500000000) ≤ -Real.log (500000000000 / 937578887141) ∧
    -Real.log (500000000000 / 937578887141) ≤ (628692803 / 1000000000) := by
  have h := checkLog_sound (w := (437578887141 / 1437578887141)) (n := 12)
    (lo := (314346401 / 500000000)) (hi := (628692803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((937578887141 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(937578887141 / 500000000000) = 1/(500000000000 / 937578887141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (314346401 / 500000000) (628692803 / 1000000000) (Real.log (937578887141 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (937578887141 / 500000000000) = -Real.log (500000000000 / 937578887141) := by
    rw [show ((937578887141 / 500000000000) : ℝ) = ((500000000000 / 937578887141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (125926387 / 200000000) ≤ -Real.log (50000000000 / 93845981231) ∧
    -Real.log (50000000000 / 93845981231) ≤ (9837999 / 15625000) := by
  have h := checkLog_sound (w := (43845981231 / 143845981231)) (n := 12)
    (lo := (125926387 / 200000000)) (hi := (9837999 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93845981231 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93845981231 / 50000000000) = 1/(50000000000 / 93845981231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (125926387 / 200000000) (9837999 / 15625000) (Real.log (93845981231 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (93845981231 / 50000000000) = -Real.log (50000000000 / 93845981231) := by
    rw [show ((93845981231 / 50000000000) : ℝ) = ((50000000000 / 93845981231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (449204163 / 1000000000) ≤ -Real.log (125000000000 / 195883070209) ∧
    -Real.log (125000000000 / 195883070209) ≤ (112301041 / 250000000) := by
  have h := checkLog_sound (w := (70883070209 / 320883070209)) (n := 12)
    (lo := (449204163 / 1000000000)) (hi := (112301041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195883070209 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195883070209 / 125000000000) = 1/(125000000000 / 195883070209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (449204163 / 1000000000) (112301041 / 250000000) (Real.log (195883070209 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (195883070209 / 125000000000) = -Real.log (125000000000 / 195883070209) := by
    rw [show ((195883070209 / 125000000000) : ℝ) = ((125000000000 / 195883070209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (224944831 / 500000000) ≤ -Real.log (250000000000 / 392034788013) ∧
    -Real.log (250000000000 / 392034788013) ≤ (449889663 / 1000000000) := by
  have h := checkLog_sound (w := (142034788013 / 642034788013)) (n := 12)
    (lo := (224944831 / 500000000)) (hi := (449889663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392034788013 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392034788013 / 250000000000) = 1/(250000000000 / 392034788013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (224944831 / 500000000) (449889663 / 1000000000) (Real.log (392034788013 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (392034788013 / 250000000000) = -Real.log (250000000000 / 392034788013) := by
    rw [show ((392034788013 / 250000000000) : ℝ) = ((250000000000 / 392034788013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0427
