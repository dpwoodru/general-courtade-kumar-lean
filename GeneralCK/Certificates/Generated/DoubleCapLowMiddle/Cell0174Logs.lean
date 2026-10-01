import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0174
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

theorem reflection_log_1_neg : (634714977 / 1000000000) ≤ -Real.log (12800 / 24147) ∧
    -Real.log (12800 / 24147) ≤ (317357489 / 500000000) := by
  have h := checkLog_sound (w := (11347 / 36947)) (n := 12)
    (lo := (634714977 / 1000000000)) (hi := (317357489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24147 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24147 / 12800) = 1/(12800 / 24147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (634714977 / 1000000000) (317357489 / 500000000) (Real.log (24147 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24147 / 12800) = -Real.log (12800 / 24147) := by
    rw [show ((24147 / 12800) : ℝ) = ((12800 / 24147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (16998553 / 7812500) ≤ -Real.log (1453 / 12800) ∧
    -Real.log (1453 / 12800) ≤ (543953697 / 250000000) := by
  have h := checkLog_sound (w := (147 / 3053)) (n := 12)
    (lo := (24093311 / 250000000)) (hi := (19274649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1453) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1453) = 1/(1453 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-543953697 / 250000000) (-16998553 / 7812500) (Real.log (1453 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (31696391 / 50000000) ≤ -Real.log (200 / 377) ∧
    -Real.log (200 / 377) ≤ (633927821 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 577)) (n := 12)
    (lo := (31696391 / 50000000)) (hi := (633927821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((377 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(377 / 200) = 1/(200 / 377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (31696391 / 50000000) (633927821 / 1000000000) (Real.log (377 / 200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (377 / 200) = -Real.log (200 / 377) := by
    rw [show ((377 / 200) : ℝ) = ((200 / 377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (540705787 / 250000000) ≤ -Real.log (23 / 200) ∧
    -Real.log (23 / 200) ≤ (135176447 / 62500000) := by
  have h := checkLog_sound (w := (1 / 24)) (n := 12)
    (lo := (10422701 / 125000000)) (hi := (83381609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 23) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25 / 23) = 1/(23 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-135176447 / 62500000) (-540705787 / 250000000) (Real.log (23 / 200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (572655401 / 1000000000) ≤ -Real.log (6400 / 11347) ∧
    -Real.log (6400 / 11347) ≤ (286327701 / 500000000) := by
  have h := checkLog_sound (w := (4947 / 17747)) (n := 12)
    (lo := (572655401 / 1000000000)) (hi := (286327701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11347 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11347 / 6400) = 1/(6400 / 11347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (572655401 / 1000000000) (286327701 / 500000000) (Real.log (11347 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11347 / 6400) = -Real.log (6400 / 11347) := by
    rw [show ((11347 / 6400) : ℝ) = ((6400 / 11347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (370666901 / 250000000) ≤ -Real.log (1453 / 6400) ∧
    -Real.log (1453 / 6400) ≤ (1482667607 / 1000000000) := by
  have h := checkLog_sound (w := (147 / 3053)) (n := 12)
    (lo := (24093311 / 250000000)) (hi := (19274649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1453) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1453) = 1/(1453 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1482667607 / 1000000000) (-370666901 / 250000000) (Real.log (1453 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (285489773 / 500000000) ≤ -Real.log (100 / 177) ∧
    -Real.log (100 / 177) ≤ (570979547 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 277)) (n := 12)
    (lo := (285489773 / 500000000)) (hi := (570979547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177 / 100) = 1/(100 / 177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (285489773 / 500000000) (570979547 / 1000000000) (Real.log (177 / 100)) := by
  have h := reflection_log_7_neg
  have he : Real.log (177 / 100) = -Real.log (100 / 177) := by
    rw [show ((177 / 100) : ℝ) = ((100 / 177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (22963687 / 15625000) ≤ -Real.log (23 / 100) ∧
    -Real.log (23 / 100) ≤ (1469675971 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 24)) (n := 12)
    (lo := (10422701 / 125000000)) (hi := (83381609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 23) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25 / 23) = 1/(23 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1469675971 / 1000000000) (-22963687 / 15625000) (Real.log (23 / 100)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (129767677 / 200000000) ≤ -Real.log (1000000 / 1913317) ∧
    -Real.log (1000000 / 1913317) ≤ (324419193 / 500000000) := by
  have h := checkLog_sound (w := (913317 / 2913317)) (n := 12)
    (lo := (129767677 / 200000000)) (hi := (324419193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1913317 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1913317 / 1000000) = 1/(1000000 / 1913317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (129767677 / 200000000) (324419193 / 500000000) (Real.log (1913317 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1913317 / 1000000) = -Real.log (1000000 / 1913317) := by
    rw [show ((1913317 / 1000000) : ℝ) = ((1000000 / 1913317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2445497491 / 1000000000) ≤ -Real.log (86683 / 1000000) ∧
    -Real.log (86683 / 1000000) ≤ (489099499 / 200000000) := by
  have h := checkLog_sound (w := (38317 / 211683)) (n := 12)
    (lo := (366055951 / 1000000000)) (hi := (22878497 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86683) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 86683) = 1/(86683 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-489099499 / 200000000) (-2445497491 / 1000000000) (Real.log (86683 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (25974039 / 40000000) ≤ -Real.log (500000 / 957149) ∧
    -Real.log (500000 / 957149) ≤ (10146109 / 15625000) := by
  have h := checkLog_sound (w := (457149 / 1457149)) (n := 12)
    (lo := (25974039 / 40000000)) (hi := (10146109 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((957149 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(957149 / 500000) = 1/(500000 / 957149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (25974039 / 40000000) (10146109 / 15625000) (Real.log (957149 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (957149 / 500000) = -Real.log (500000 / 957149) := by
    rw [show ((957149 / 500000) : ℝ) = ((500000 / 957149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1228439557 / 500000000) ≤ -Real.log (42851 / 500000) ∧
    -Real.log (42851 / 500000) ≤ (1228439559 / 500000000) := by
  have h := checkLog_sound (w := (19649 / 105351)) (n := 12)
    (lo := (188718787 / 500000000)) (hi := (15097503 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42851) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 42851) = 1/(42851 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1228439559 / 500000000) (-1228439557 / 500000000) (Real.log (42851 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (323560521 / 500000000) ≤ -Real.log (500000 / 955017) ∧
    -Real.log (500000 / 955017) ≤ (647121043 / 1000000000) := by
  have h := checkLog_sound (w := (455017 / 1455017)) (n := 12)
    (lo := (323560521 / 500000000)) (hi := (647121043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((955017 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(955017 / 500000) = 1/(500000 / 955017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (323560521 / 500000000) (647121043 / 1000000000) (Real.log (955017 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (955017 / 500000) = -Real.log (500000 / 955017) := by
    rw [show ((955017 / 500000) : ℝ) = ((500000 / 955017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (18815027 / 7812500) ≤ -Real.log (44983 / 500000) ∧
    -Real.log (44983 / 500000) ≤ (120416173 / 50000000) := by
  have h := checkLog_sound (w := (17517 / 107483)) (n := 12)
    (lo := (82220479 / 250000000)) (hi := (328881917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44983) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 44983) = 1/(44983 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-120416173 / 50000000) (-18815027 / 7812500) (Real.log (44983 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (323843159 / 500000000) ≤ -Real.log (500000 / 955557) ∧
    -Real.log (500000 / 955557) ≤ (647686319 / 1000000000) := by
  have h := checkLog_sound (w := (455557 / 1455557)) (n := 12)
    (lo := (323843159 / 500000000)) (hi := (647686319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((955557 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(955557 / 500000) = 1/(500000 / 955557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (323843159 / 500000000) (647686319 / 1000000000) (Real.log (955557 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (955557 / 500000) = -Real.log (500000 / 955557) := by
    rw [show ((955557 / 500000) : ℝ) = ((500000 / 955557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2420400627 / 1000000000) ≤ -Real.log (44443 / 500000) ∧
    -Real.log (44443 / 500000) ≤ (2420400631 / 1000000000) := by
  have h := checkLog_sound (w := (18057 / 106943)) (n := 12)
    (lo := (340959087 / 1000000000)) (hi := (21309943 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44443) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 44443) = 1/(44443 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2420400631 / 1000000000) (-2420400627 / 1000000000) (Real.log (44443 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (24754687 / 8000000) ≤ -Real.log (500000000000 / 11036287391991) ∧
    -Real.log (500000000000 / 11036287391991) ≤ (77358397 / 25000000) := by
  have h := checkLog_sound (w := (3036287391991 / 19036287391991)) (n := 12)
    (lo := (64349431 / 200000000)) (hi := (80436789 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11036287391991 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11036287391991 / 8000000000000) = 1/(500000000000 / 11036287391991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (24754687 / 8000000) (77358397 / 25000000) (Real.log (11036287391991 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11036287391991 / 500000000000) = -Real.log (500000000000 / 11036287391991) := by
    rw [show ((11036287391991 / 500000000000) : ℝ) = ((500000000000 / 11036287391991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3106230089 / 1000000000) ≤ -Real.log (500000000000 / 11168339128609) ∧
    -Real.log (500000000000 / 11168339128609) ≤ (1553115047 / 500000000) := by
  have h := checkLog_sound (w := (3168339128609 / 19168339128609)) (n := 12)
    (lo := (333641369 / 1000000000)) (hi := (33364137 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11168339128609 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11168339128609 / 8000000000000) = 1/(500000000000 / 11168339128609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3106230089 / 1000000000) (1553115047 / 500000000) (Real.log (11168339128609 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11168339128609 / 500000000000) = -Real.log (500000000000 / 11168339128609) := by
    rw [show ((11168339128609 / 500000000000) : ℝ) = ((500000000000 / 11168339128609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1527722249 / 500000000) ≤ -Real.log (125000000000 / 2653827557077) ∧
    -Real.log (125000000000 / 2653827557077) ≤ (3055444503 / 1000000000) := by
  have h := checkLog_sound (w := (653827557077 / 4653827557077)) (n := 12)
    (lo := (141427889 / 500000000)) (hi := (282855779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2653827557077 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2653827557077 / 2000000000000) = 1/(125000000000 / 2653827557077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1527722249 / 500000000) (3055444503 / 1000000000) (Real.log (2653827557077 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2653827557077 / 125000000000) = -Real.log (125000000000 / 2653827557077) := by
    rw [show ((2653827557077 / 125000000000) : ℝ) = ((125000000000 / 2653827557077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (613617389 / 200000000) ≤ -Real.log (125000000000 / 2687591409221) ∧
    -Real.log (125000000000 / 2687591409221) ≤ (61361739 / 20000000) := by
  have h := checkLog_sound (w := (687591409221 / 4687591409221)) (n := 12)
    (lo := (11819929 / 40000000)) (hi := (147749113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2687591409221 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2687591409221 / 2000000000000) = 1/(125000000000 / 2687591409221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (613617389 / 200000000) (61361739 / 20000000) (Real.log (2687591409221 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2687591409221 / 125000000000) = -Real.log (125000000000 / 2687591409221) := by
    rw [show ((2687591409221 / 125000000000) : ℝ) = ((125000000000 / 2687591409221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0174
