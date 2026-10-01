import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0193
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

theorem reflection_log_1_neg : (605169427 / 1000000000) ≤ -Real.log (3200 / 5861) ∧
    -Real.log (3200 / 5861) ≤ (151292357 / 250000000) := by
  have h := checkLog_sound (w := (2661 / 9061)) (n := 12)
    (lo := (605169427 / 1000000000)) (hi := (151292357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5861 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5861 / 3200) = 1/(3200 / 5861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (605169427 / 1000000000) (151292357 / 250000000) (Real.log (5861 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5861 / 3200) = -Real.log (3200 / 5861) := by
    rw [show ((5861 / 3200) : ℝ) = ((3200 / 5861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (445297629 / 250000000) ≤ -Real.log (539 / 3200) ∧
    -Real.log (539 / 3200) ≤ (1781190519 / 1000000000) := by
  have h := checkLog_sound (w := (261 / 1339)) (n := 12)
    (lo := (98724039 / 250000000)) (hi := (394896157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 539) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 539) = 1/(539 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1781190519 / 1000000000) (-445297629 / 250000000) (Real.log (539 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (150886807 / 250000000) ≤ -Real.log (6400 / 11703) ∧
    -Real.log (6400 / 11703) ≤ (603547229 / 1000000000) := by
  have h := checkLog_sound (w := (5303 / 18103)) (n := 12)
    (lo := (150886807 / 250000000)) (hi := (603547229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11703 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11703 / 6400) = 1/(6400 / 11703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (150886807 / 250000000) (603547229 / 1000000000) (Real.log (11703 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11703 / 6400) = -Real.log (6400 / 11703) := by
    rw [show ((11703 / 6400) : ℝ) = ((6400 / 11703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1763718807 / 1000000000) ≤ -Real.log (1097 / 6400) ∧
    -Real.log (1097 / 6400) ≤ (176371881 / 100000000) := by
  have h := checkLog_sound (w := (503 / 2697)) (n := 12)
    (lo := (377424447 / 1000000000)) (hi := (5897257 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1097) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1097) = 1/(1097 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-176371881 / 100000000) (-1763718807 / 1000000000) (Real.log (1097 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (254349181 / 500000000) ≤ -Real.log (1600 / 2661) ∧
    -Real.log (1600 / 2661) ≤ (508698363 / 1000000000) := by
  have h := checkLog_sound (w := (1061 / 4261)) (n := 12)
    (lo := (254349181 / 500000000)) (hi := (508698363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2661 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2661 / 1600) = 1/(1600 / 2661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (254349181 / 500000000) (508698363 / 1000000000) (Real.log (2661 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2661 / 1600) = -Real.log (1600 / 2661) := by
    rw [show ((2661 / 1600) : ℝ) = ((1600 / 2661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (136005417 / 125000000) ≤ -Real.log (539 / 1600) ∧
    -Real.log (539 / 1600) ≤ (544021669 / 500000000) := by
  have h := checkLog_sound (w := (261 / 1339)) (n := 12)
    (lo := (98724039 / 250000000)) (hi := (394896157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 539) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 539) = 1/(539 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-544021669 / 500000000) (-136005417 / 125000000) (Real.log (539 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (15785059 / 31250000) ≤ -Real.log (3200 / 5303) ∧
    -Real.log (3200 / 5303) ≤ (505121889 / 1000000000) := by
  have h := checkLog_sound (w := (2103 / 8503)) (n := 12)
    (lo := (15785059 / 31250000)) (hi := (505121889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5303 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5303 / 3200) = 1/(3200 / 5303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (15785059 / 31250000) (505121889 / 1000000000) (Real.log (5303 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5303 / 3200) = -Real.log (3200 / 5303) := by
    rw [show ((5303 / 3200) : ℝ) = ((3200 / 5303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1070571627 / 1000000000) ≤ -Real.log (1097 / 3200) ∧
    -Real.log (1097 / 3200) ≤ (1070571629 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 2697)) (n := 12)
    (lo := (377424447 / 1000000000)) (hi := (5897257 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1097) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1097) = 1/(1097 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1070571629 / 1000000000) (-1070571627 / 1000000000) (Real.log (1097 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (315231203 / 500000000) ≤ -Real.log (1000000 / 1878479) ∧
    -Real.log (1000000 / 1878479) ≤ (630462407 / 1000000000) := by
  have h := checkLog_sound (w := (878479 / 2878479)) (n := 12)
    (lo := (315231203 / 500000000)) (hi := (630462407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1878479 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1878479 / 1000000) = 1/(1000000 / 1878479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (315231203 / 500000000) (630462407 / 1000000000) (Real.log (1878479 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1878479 / 1000000) = -Real.log (1000000 / 1878479) := by
    rw [show ((1878479 / 1000000) : ℝ) = ((1000000 / 1878479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2107668189 / 1000000000) ≤ -Real.log (121521 / 1000000) ∧
    -Real.log (121521 / 1000000) ≤ (2107668193 / 1000000000) := by
  have h := checkLog_sound (w := (3479 / 246521)) (n := 12)
    (lo := (28226649 / 1000000000)) (hi := (564533 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 121521) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 121521) = 1/(121521 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2107668193 / 1000000000) (-2107668189 / 1000000000) (Real.log (121521 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (315687747 / 500000000) ≤ -Real.log (200000 / 376039) ∧
    -Real.log (200000 / 376039) ≤ (126275099 / 200000000) := by
  have h := checkLog_sound (w := (176039 / 576039)) (n := 12)
    (lo := (315687747 / 500000000)) (hi := (126275099 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376039 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376039 / 200000) = 1/(200000 / 376039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (315687747 / 500000000) (126275099 / 200000000) (Real.log (376039 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (376039 / 200000) = -Real.log (200000 / 376039) := by
    rw [show ((376039 / 200000) : ℝ) = ((200000 / 376039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (33154529 / 15625000) ≤ -Real.log (23961 / 200000) ∧
    -Real.log (23961 / 200000) ≤ (106094493 / 50000000) := by
  have h := checkLog_sound (w := (1039 / 48961)) (n := 12)
    (lo := (10612079 / 250000000)) (hi := (42448317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 23961) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 23961) = 1/(23961 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-106094493 / 50000000) (-33154529 / 15625000) (Real.log (23961 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (39121319 / 62500000) ≤ -Real.log (200000 / 374001) ∧
    -Real.log (200000 / 374001) ≤ (125188221 / 200000000) := by
  have h := checkLog_sound (w := (174001 / 574001)) (n := 12)
    (lo := (39121319 / 62500000)) (hi := (125188221 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374001 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374001 / 200000) = 1/(200000 / 374001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (39121319 / 62500000) (125188221 / 200000000) (Real.log (374001 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (374001 / 200000) = -Real.log (200000 / 374001) := by
    rw [show ((374001 / 200000) : ℝ) = ((200000 / 374001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2040259289 / 1000000000) ≤ -Real.log (25999 / 200000) ∧
    -Real.log (25999 / 200000) ≤ (510064823 / 250000000) := by
  have h := checkLog_sound (w := (24001 / 75999)) (n := 12)
    (lo := (653964929 / 1000000000)) (hi := (65396493 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 25999) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 25999) = 1/(25999 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-510064823 / 250000000) (-2040259289 / 1000000000) (Real.log (25999 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (156761059 / 250000000) ≤ -Real.log (1000000 / 1872069) ∧
    -Real.log (1000000 / 1872069) ≤ (627044237 / 1000000000) := by
  have h := checkLog_sound (w := (872069 / 2872069)) (n := 12)
    (lo := (156761059 / 250000000)) (hi := (627044237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1872069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1872069 / 1000000) = 1/(1000000 / 1872069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (156761059 / 250000000) (627044237 / 1000000000) (Real.log (1872069 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1872069 / 1000000) = -Real.log (1000000 / 1872069) := by
    rw [show ((1872069 / 1000000) : ℝ) = ((1000000 / 1872069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2056264221 / 1000000000) ≤ -Real.log (127931 / 1000000) ∧
    -Real.log (127931 / 1000000) ≤ (64258257 / 31250000) := by
  have h := checkLog_sound (w := (122069 / 377931)) (n := 12)
    (lo := (669969861 / 1000000000)) (hi := (334984931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 127931) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 127931) = 1/(127931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-64258257 / 31250000) (-2056264221 / 1000000000) (Real.log (127931 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (684532649 / 250000000) ≤ -Real.log (500000000000 / 7729030373351) ∧
    -Real.log (500000000000 / 7729030373351) ≤ (13690653 / 5000000) := by
  have h := checkLog_sound (w := (3729030373351 / 11729030373351)) (n := 12)
    (lo := (20584033 / 31250000)) (hi := (658689057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7729030373351 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7729030373351 / 4000000000000) = 1/(500000000000 / 7729030373351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (684532649 / 250000000) (13690653 / 5000000) (Real.log (7729030373351 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7729030373351 / 500000000000) = -Real.log (500000000000 / 7729030373351) := by
    rw [show ((7729030373351 / 500000000000) : ℝ) = ((500000000000 / 7729030373351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2753265351 / 1000000000) ≤ -Real.log (20000000000 / 313875881641) ∧
    -Real.log (20000000000 / 313875881641) ≤ (550653071 / 200000000) := by
  have h := checkLog_sound (w := (153875881641 / 473875881641)) (n := 12)
    (lo := (673823811 / 1000000000)) (hi := (168455953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313875881641 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(313875881641 / 160000000000) = 1/(20000000000 / 313875881641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2753265351 / 1000000000) (550653071 / 200000000) (Real.log (313875881641 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (313875881641 / 20000000000) = -Real.log (20000000000 / 313875881641) := by
    rw [show ((313875881641 / 20000000000) : ℝ) = ((20000000000 / 313875881641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2666200393 / 1000000000) ≤ -Real.log (20000000000 / 287704142467) ∧
    -Real.log (20000000000 / 287704142467) ≤ (2666200397 / 1000000000) := by
  have h := checkLog_sound (w := (127704142467 / 447704142467)) (n := 12)
    (lo := (586758853 / 1000000000)) (hi := (293379427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287704142467 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(287704142467 / 160000000000) = 1/(20000000000 / 287704142467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2666200393 / 1000000000) (2666200397 / 1000000000) (Real.log (287704142467 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (287704142467 / 20000000000) = -Real.log (20000000000 / 287704142467) := by
    rw [show ((287704142467 / 20000000000) : ℝ) = ((20000000000 / 287704142467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2683308457 / 1000000000) ≤ -Real.log (125000000000 / 1829178424307) ∧
    -Real.log (125000000000 / 1829178424307) ≤ (2683308461 / 1000000000) := by
  have h := checkLog_sound (w := (829178424307 / 2829178424307)) (n := 12)
    (lo := (603866917 / 1000000000)) (hi := (301933459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1829178424307 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1829178424307 / 1000000000000) = 1/(125000000000 / 1829178424307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2683308457 / 1000000000) (2683308461 / 1000000000) (Real.log (1829178424307 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1829178424307 / 125000000000) = -Real.log (125000000000 / 1829178424307) := by
    rw [show ((1829178424307 / 125000000000) : ℝ) = ((125000000000 / 1829178424307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0193
