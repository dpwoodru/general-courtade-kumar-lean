import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0202
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

theorem reflection_log_1_neg : (585527169 / 1000000000) ≤ -Real.log (3200 / 5747) ∧
    -Real.log (3200 / 5747) ≤ (58552717 / 100000000) := by
  have h := checkLog_sound (w := (2547 / 8947)) (n := 12)
    (lo := (585527169 / 1000000000)) (hi := (58552717 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5747 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5747 / 3200) = 1/(3200 / 5747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (585527169 / 1000000000) (58552717 / 100000000) (Real.log (5747 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5747 / 3200) = -Real.log (3200 / 5747) := by
    rw [show ((5747 / 3200) : ℝ) = ((3200 / 5747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (794664479 / 500000000) ≤ -Real.log (653 / 3200) ∧
    -Real.log (653 / 3200) ≤ (1589328961 / 1000000000) := by
  have h := checkLog_sound (w := (147 / 1453)) (n := 12)
    (lo := (101517299 / 500000000)) (hi := (203034599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 653) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 653) = 1/(653 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1589328961 / 1000000000) (-794664479 / 500000000) (Real.log (653 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (582215619 / 1000000000) ≤ -Real.log (100 / 179) ∧
    -Real.log (100 / 179) ≤ (29110781 / 50000000) := by
  have h := checkLog_sound (w := (79 / 279)) (n := 12)
    (lo := (582215619 / 1000000000)) (hi := (29110781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179 / 100) = 1/(100 / 179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (582215619 / 1000000000) (29110781 / 50000000) (Real.log (179 / 100)) := by
  have h := reflection_log_3_neg
  have he : Real.log (179 / 100) = -Real.log (100 / 179) := by
    rw [show ((179 / 100) : ℝ) = ((100 / 179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1560647747 / 1000000000) ≤ -Real.log (21 / 100) ∧
    -Real.log (21 / 100) ≤ (6242591 / 4000000) := by
  have h := checkLog_sound (w := (2 / 23)) (n := 12)
    (lo := (174353387 / 1000000000)) (hi := (43588347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 21) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25 / 21) = 1/(21 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6242591 / 4000000) (-1560647747 / 1000000000) (Real.log (21 / 100)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (232456283 / 500000000) ≤ -Real.log (1600 / 2547) ∧
    -Real.log (1600 / 2547) ≤ (464912567 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 4147)) (n := 12)
    (lo := (232456283 / 500000000)) (hi := (464912567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2547 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2547 / 1600) = 1/(1600 / 2547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (232456283 / 500000000) (464912567 / 1000000000) (Real.log (2547 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2547 / 1600) = -Real.log (1600 / 2547) := by
    rw [show ((2547 / 1600) : ℝ) = ((1600 / 2547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (448090889 / 500000000) ≤ -Real.log (653 / 1600) ∧
    -Real.log (653 / 1600) ≤ (44809089 / 50000000) := by
  have h := checkLog_sound (w := (147 / 1453)) (n := 12)
    (lo := (101517299 / 500000000)) (hi := (203034599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 653) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 653) = 1/(653 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-44809089 / 50000000) (-448090889 / 500000000) (Real.log (653 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (457424847 / 1000000000) ≤ -Real.log (50 / 79) ∧
    -Real.log (50 / 79) ≤ (28589053 / 62500000) := by
  have h := checkLog_sound (w := (29 / 129)) (n := 12)
    (lo := (457424847 / 1000000000)) (hi := (28589053 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79 / 50) = 1/(50 / 79) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (457424847 / 1000000000) (28589053 / 62500000) (Real.log (79 / 50)) := by
  have h := reflection_log_7_neg
  have he : Real.log (79 / 50) = -Real.log (50 / 79) := by
    rw [show ((79 / 50) : ℝ) = ((50 / 79) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (867500567 / 1000000000) ≤ -Real.log (21 / 50) ∧
    -Real.log (21 / 50) ≤ (867500569 / 1000000000) := by
  have h := checkLog_sound (w := (2 / 23)) (n := 12)
    (lo := (174353387 / 1000000000)) (hi := (43588347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 21) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25 / 21) = 1/(21 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-867500569 / 1000000000) (-867500567 / 1000000000) (Real.log (21 / 50)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (619181967 / 1000000000) ≤ -Real.log (15625 / 29022) ∧
    -Real.log (15625 / 29022) ≤ (38698873 / 62500000) := by
  have h := checkLog_sound (w := (13397 / 44647)) (n := 12)
    (lo := (619181967 / 1000000000)) (hi := (38698873 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29022 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29022 / 15625) = 1/(15625 / 29022) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (619181967 / 1000000000) (38698873 / 62500000) (Real.log (29022 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (29022 / 15625) = -Real.log (15625 / 29022) := by
    rw [show ((29022 / 15625) : ℝ) = ((15625 / 29022) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (30433873 / 15625000) ≤ -Real.log (2228 / 15625) ∧
    -Real.log (2228 / 15625) ≤ (15582143 / 8000000) := by
  have h := checkLog_sound (w := (6713 / 24537)) (n := 12)
    (lo := (70184189 / 125000000)) (hi := (561473513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8912) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 8912) = 1/(2228 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-15582143 / 8000000) (-30433873 / 15625000) (Real.log (2228 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (310422903 / 500000000) ≤ -Real.log (1000000 / 1860501) ∧
    -Real.log (1000000 / 1860501) ≤ (620845807 / 1000000000) := by
  have h := checkLog_sound (w := (860501 / 2860501)) (n := 12)
    (lo := (310422903 / 500000000)) (hi := (620845807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1860501 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1860501 / 1000000) = 1/(1000000 / 1860501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (310422903 / 500000000) (620845807 / 1000000000) (Real.log (1860501 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1860501 / 1000000) = -Real.log (1000000 / 1860501) := by
    rw [show ((1860501 / 1000000) : ℝ) = ((1000000 / 1860501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (393939569 / 200000000) ≤ -Real.log (139499 / 1000000) ∧
    -Real.log (139499 / 1000000) ≤ (246212231 / 125000000) := by
  have h := checkLog_sound (w := (110501 / 389499)) (n := 12)
    (lo := (116680697 / 200000000)) (hi := (291701743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 139499) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 139499) = 1/(139499 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-246212231 / 125000000) (-393939569 / 200000000) (Real.log (139499 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (305848971 / 500000000) ≤ -Real.log (1000000 / 1843559) ∧
    -Real.log (1000000 / 1843559) ≤ (611697943 / 1000000000) := by
  have h := checkLog_sound (w := (843559 / 2843559)) (n := 12)
    (lo := (305848971 / 500000000)) (hi := (611697943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1843559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1843559 / 1000000) = 1/(1000000 / 1843559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (305848971 / 500000000) (611697943 / 1000000000) (Real.log (1843559 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1843559 / 1000000) = -Real.log (1000000 / 1843559) := by
    rw [show ((1843559 / 1000000) : ℝ) = ((1000000 / 1843559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (371015267 / 200000000) ≤ -Real.log (156441 / 1000000) ∧
    -Real.log (156441 / 1000000) ≤ (927538169 / 500000000) := by
  have h := checkLog_sound (w := (93559 / 406441)) (n := 12)
    (lo := (18751279 / 40000000)) (hi := (58597747 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 156441) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 156441) = 1/(156441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-927538169 / 500000000) (-371015267 / 200000000) (Real.log (156441 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (30693969 / 50000000) ≤ -Real.log (200000 / 369517) ∧
    -Real.log (200000 / 369517) ≤ (613879381 / 1000000000) := by
  have h := checkLog_sound (w := (169517 / 569517)) (n := 12)
    (lo := (30693969 / 50000000)) (hi := (613879381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369517 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369517 / 200000) = 1/(200000 / 369517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (30693969 / 50000000) (613879381 / 1000000000) (Real.log (369517 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (369517 / 200000) = -Real.log (200000 / 369517) := by
    rw [show ((369517 / 200000) : ℝ) = ((200000 / 369517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (940574107 / 500000000) ≤ -Real.log (30483 / 200000) ∧
    -Real.log (30483 / 200000) ≤ (1881148217 / 1000000000) := by
  have h := checkLog_sound (w := (19517 / 80483)) (n := 12)
    (lo := (247426927 / 500000000)) (hi := (98970771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 30483) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 30483) = 1/(30483 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1881148217 / 1000000000) (-940574107 / 500000000) (Real.log (30483 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2566949839 / 1000000000) ≤ -Real.log (500000000000 / 6513016157989) ∧
    -Real.log (500000000000 / 6513016157989) ≤ (2566949843 / 1000000000) := by
  have h := checkLog_sound (w := (2513016157989 / 10513016157989)) (n := 12)
    (lo := (487508299 / 1000000000)) (hi := (4875083 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6513016157989 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6513016157989 / 4000000000000) = 1/(500000000000 / 6513016157989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2566949839 / 1000000000) (2566949843 / 1000000000) (Real.log (6513016157989 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6513016157989 / 500000000000) = -Real.log (500000000000 / 6513016157989) := by
    rw [show ((6513016157989 / 500000000000) : ℝ) = ((500000000000 / 6513016157989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (51810873 / 20000000) ≤ -Real.log (125000000000 / 1667127542133) ∧
    -Real.log (125000000000 / 1667127542133) ≤ (1295271827 / 500000000) := by
  have h := checkLog_sound (w := (667127542133 / 2667127542133)) (n := 12)
    (lo := (51110211 / 100000000)) (hi := (511102111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1667127542133 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1667127542133 / 1000000000000) = 1/(125000000000 / 1667127542133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (51810873 / 20000000) (1295271827 / 500000000) (Real.log (1667127542133 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1667127542133 / 125000000000) = -Real.log (125000000000 / 1667127542133) := by
    rw [show ((1667127542133 / 125000000000) : ℝ) = ((125000000000 / 1667127542133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2466774277 / 1000000000) ≤ -Real.log (500000000000 / 5892186191599) ∧
    -Real.log (500000000000 / 5892186191599) ≤ (2466774281 / 1000000000) := by
  have h := checkLog_sound (w := (1892186191599 / 9892186191599)) (n := 12)
    (lo := (387332737 / 1000000000)) (hi := (193666369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5892186191599 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5892186191599 / 4000000000000) = 1/(500000000000 / 5892186191599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2466774277 / 1000000000) (2466774281 / 1000000000) (Real.log (5892186191599 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5892186191599 / 500000000000) = -Real.log (500000000000 / 5892186191599) := by
    rw [show ((5892186191599 / 500000000000) : ℝ) = ((500000000000 / 5892186191599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1247513797 / 500000000) ≤ -Real.log (250000000000 / 3030517009481) ∧
    -Real.log (250000000000 / 3030517009481) ≤ (1247513799 / 500000000) := by
  have h := checkLog_sound (w := (1030517009481 / 5030517009481)) (n := 12)
    (lo := (207793027 / 500000000)) (hi := (83117211 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3030517009481 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3030517009481 / 2000000000000) = 1/(250000000000 / 3030517009481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1247513797 / 500000000) (1247513799 / 500000000) (Real.log (3030517009481 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3030517009481 / 250000000000) = -Real.log (250000000000 / 3030517009481) := by
    rw [show ((3030517009481 / 250000000000) : ℝ) = ((250000000000 / 3030517009481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0202
