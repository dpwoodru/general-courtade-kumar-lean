import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0067
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

theorem reflection_log_1_neg : (135491669 / 200000000) ≤ -Real.log (25600 / 50403) ∧
    -Real.log (25600 / 50403) ≤ (338729173 / 500000000) := by
  have h := checkLog_sound (w := (24803 / 76003)) (n := 12)
    (lo := (135491669 / 200000000)) (hi := (338729173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50403 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50403 / 25600) = 1/(25600 / 50403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (135491669 / 200000000) (338729173 / 500000000) (Real.log (50403 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50403 / 25600) = -Real.log (25600 / 50403) := by
    rw [show ((50403 / 25600) : ℝ) = ((25600 / 50403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (867373237 / 250000000) ≤ -Real.log (797 / 25600) ∧
    -Real.log (797 / 25600) ≤ (1734746477 / 500000000) := by
  have h := checkLog_sound (w := (3 / 1597)) (n := 12)
    (lo := (469631 / 125000000)) (hi := (3757049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 797) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 797) = 1/(797 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1734746477 / 500000000) (-867373237 / 250000000) (Real.log (797 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (6773641 / 10000000) ≤ -Real.log (102400 / 201593) ∧
    -Real.log (102400 / 201593) ≤ (677364101 / 1000000000) := by
  have h := checkLog_sound (w := (99193 / 303993)) (n := 12)
    (lo := (6773641 / 10000000)) (hi := (677364101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201593 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201593 / 102400) = 1/(102400 / 201593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (6773641 / 10000000) (677364101 / 1000000000) (Real.log (201593 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201593 / 102400) = -Real.log (102400 / 201593) := by
    rw [show ((201593 / 102400) : ℝ) = ((102400 / 201593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3463550789 / 1000000000) ≤ -Real.log (3207 / 102400) ∧
    -Real.log (3207 / 102400) ≤ (1731775397 / 500000000) := by
  have h := checkLog_sound (w := (3193 / 9607)) (n := 12)
    (lo := (690962069 / 1000000000)) (hi := (69096207 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 3207) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 3207) = 1/(3207 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1731775397 / 500000000) (-3463550789 / 1000000000) (Real.log (3207 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (330759721 / 500000000) ≤ -Real.log (12800 / 24803) ∧
    -Real.log (12800 / 24803) ≤ (661519443 / 1000000000) := by
  have h := checkLog_sound (w := (12003 / 37603)) (n := 12)
    (lo := (330759721 / 500000000)) (hi := (661519443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24803 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24803 / 12800) = 1/(12800 / 24803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (330759721 / 500000000) (661519443 / 1000000000) (Real.log (24803 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24803 / 12800) = -Real.log (12800 / 24803) := by
    rw [show ((24803 / 12800) : ℝ) = ((12800 / 24803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (347043221 / 125000000) ≤ -Real.log (797 / 12800) ∧
    -Real.log (797 / 12800) ≤ (2776345773 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 1597)) (n := 12)
    (lo := (469631 / 125000000)) (hi := (3757049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 797) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 797) = 1/(797 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2776345773 / 1000000000) (-347043221 / 125000000) (Real.log (797 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (132265583 / 200000000) ≤ -Real.log (51200 / 99193) ∧
    -Real.log (51200 / 99193) ≤ (165331979 / 250000000) := by
  have h := checkLog_sound (w := (47993 / 150393)) (n := 12)
    (lo := (132265583 / 200000000)) (hi := (165331979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99193 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99193 / 51200) = 1/(51200 / 99193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (132265583 / 200000000) (165331979 / 250000000) (Real.log (99193 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99193 / 51200) = -Real.log (51200 / 99193) := by
    rw [show ((99193 / 51200) : ℝ) = ((51200 / 99193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2770403609 / 1000000000) ≤ -Real.log (3207 / 51200) ∧
    -Real.log (3207 / 51200) ≤ (2770403613 / 1000000000) := by
  have h := checkLog_sound (w := (3193 / 9607)) (n := 12)
    (lo := (690962069 / 1000000000)) (hi := (69096207 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 3207) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6400 / 3207) = 1/(3207 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2770403613 / 1000000000) (-2770403609 / 1000000000) (Real.log (3207 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135999419 / 200000000) ≤ -Real.log (62500 / 123367) ∧
    -Real.log (62500 / 123367) ≤ (84999637 / 125000000) := by
  have h := checkLog_sound (w := (60867 / 185867)) (n := 12)
    (lo := (135999419 / 200000000)) (hi := (84999637 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123367 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123367 / 62500) = 1/(62500 / 123367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135999419 / 200000000) (84999637 / 125000000) (Real.log (123367 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (123367 / 62500) = -Real.log (62500 / 123367) := by
    rw [show ((123367 / 62500) : ℝ) = ((62500 / 123367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3644747739 / 1000000000) ≤ -Real.log (1633 / 62500) ∧
    -Real.log (1633 / 62500) ≤ (728949549 / 200000000) := by
  have h := checkLog_sound (w := (2561 / 28689)) (n := 12)
    (lo := (179011839 / 1000000000)) (hi := (139853 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13064) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13064) = 1/(1633 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-728949549 / 200000000) (-3644747739 / 1000000000) (Real.log (1633 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (85009009 / 125000000) ≤ -Real.log (50000 / 98701) ∧
    -Real.log (50000 / 98701) ≤ (680072073 / 1000000000) := by
  have h := checkLog_sound (w := (48701 / 148701)) (n := 12)
    (lo := (85009009 / 125000000)) (hi := (680072073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98701 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98701 / 50000) = 1/(50000 / 98701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (85009009 / 125000000) (680072073 / 1000000000) (Real.log (98701 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (98701 / 50000) = -Real.log (50000 / 98701) := by
    rw [show ((98701 / 50000) : ℝ) = ((50000 / 98701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (456303533 / 125000000) ≤ -Real.log (1299 / 50000) ∧
    -Real.log (1299 / 50000) ≤ (365042827 / 100000000) := by
  have h := checkLog_sound (w := (527 / 5723)) (n := 12)
    (lo := (46173091 / 250000000)) (hi := (36938473 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2598) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2598) = 1/(1299 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-365042827 / 100000000) (-456303533 / 125000000) (Real.log (1299 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (679912487 / 1000000000) ≤ -Real.log (200000 / 394741) ∧
    -Real.log (200000 / 394741) ≤ (84989061 / 125000000) := by
  have h := checkLog_sound (w := (194741 / 594741)) (n := 12)
    (lo := (679912487 / 1000000000)) (hi := (84989061 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394741 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394741 / 200000) = 1/(200000 / 394741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (679912487 / 1000000000) (84989061 / 125000000) (Real.log (394741 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (394741 / 200000) = -Real.log (200000 / 394741) := by
    rw [show ((394741 / 200000) : ℝ) = ((200000 / 394741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3638376469 / 1000000000) ≤ -Real.log (5259 / 200000) ∧
    -Real.log (5259 / 200000) ≤ (145535059 / 40000000) := by
  have h := checkLog_sound (w := (991 / 11509)) (n := 12)
    (lo := (172640569 / 1000000000)) (hi := (17264057 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5259) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5259) = 1/(5259 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-145535059 / 40000000) (-3638376469 / 1000000000) (Real.log (5259 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (679988483 / 1000000000) ≤ -Real.log (200000 / 394771) ∧
    -Real.log (200000 / 394771) ≤ (169997121 / 250000000) := by
  have h := checkLog_sound (w := (194771 / 594771)) (n := 12)
    (lo := (679988483 / 1000000000)) (hi := (169997121 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394771 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394771 / 200000) = 1/(200000 / 394771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (679988483 / 1000000000) (169997121 / 250000000) (Real.log (394771 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (394771 / 200000) = -Real.log (200000 / 394771) := by
    rw [show ((394771 / 200000) : ℝ) = ((200000 / 394771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (911024327 / 250000000) ≤ -Real.log (5229 / 200000) ∧
    -Real.log (5229 / 200000) ≤ (1822048657 / 500000000) := by
  have h := checkLog_sound (w := (1021 / 11479)) (n := 12)
    (lo := (2786897 / 15625000)) (hi := (178361409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5229) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5229) = 1/(5229 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1822048657 / 500000000) (-911024327 / 250000000) (Real.log (5229 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (864948967 / 200000000) ≤ -Real.log (100000000000 / 7554623392529) ∧
    -Real.log (100000000000 / 7554623392529) ≤ (2162372421 / 500000000) := by
  have h := checkLog_sound (w := (1154623392529 / 13954623392529)) (n := 12)
    (lo := (33172351 / 200000000)) (hi := (41465439 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7554623392529 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7554623392529 / 6400000000000) = 1/(100000000000 / 7554623392529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (864948967 / 200000000) (2162372421 / 500000000) (Real.log (7554623392529 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7554623392529 / 100000000000) = -Real.log (100000000000 / 7554623392529) := by
    rw [show ((7554623392529 / 100000000000) : ℝ) = ((100000000000 / 7554623392529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4330500337 / 1000000000) ≤ -Real.log (250000000000 / 18995573518091) ∧
    -Real.log (250000000000 / 18995573518091) ≤ (541312543 / 125000000) := by
  have h := checkLog_sound (w := (2995573518091 / 34995573518091)) (n := 12)
    (lo := (171617257 / 1000000000)) (hi := (85808629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18995573518091 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18995573518091 / 16000000000000) = 1/(250000000000 / 18995573518091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4330500337 / 1000000000) (541312543 / 125000000) (Real.log (18995573518091 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (18995573518091 / 250000000000) = -Real.log (250000000000 / 18995573518091) := by
    rw [show ((18995573518091 / 250000000000) : ℝ) = ((250000000000 / 18995573518091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (863657791 / 200000000) ≤ -Real.log (10000000000 / 750600874691) ∧
    -Real.log (10000000000 / 750600874691) ≤ (2159144481 / 500000000) := by
  have h := checkLog_sound (w := (110600874691 / 1390600874691)) (n := 12)
    (lo := (1275247 / 8000000)) (hi := (39851469 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750600874691 / 640000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(750600874691 / 640000000000) = 1/(10000000000 / 750600874691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (863657791 / 200000000) (2159144481 / 500000000) (Real.log (750600874691 / 10000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (750600874691 / 10000000000) = -Real.log (10000000000 / 750600874691) := by
    rw [show ((750600874691 / 10000000000) : ℝ) = ((10000000000 / 750600874691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4324085791 / 1000000000) ≤ -Real.log (125000000000 / 9437057754829) ∧
    -Real.log (125000000000 / 9437057754829) ≤ (2162042899 / 500000000) := by
  have h := checkLog_sound (w := (1437057754829 / 17437057754829)) (n := 12)
    (lo := (165202711 / 1000000000)) (hi := (20650339 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9437057754829 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9437057754829 / 8000000000000) = 1/(125000000000 / 9437057754829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4324085791 / 1000000000) (2162042899 / 500000000) (Real.log (9437057754829 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (9437057754829 / 125000000000) = -Real.log (125000000000 / 9437057754829) := by
    rw [show ((9437057754829 / 125000000000) : ℝ) = ((125000000000 / 9437057754829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0067
