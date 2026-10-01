import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0094
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

theorem reflection_log_1_neg : (168136449 / 250000000) ≤ -Real.log (6400 / 12539) ∧
    -Real.log (6400 / 12539) ≤ (672545797 / 1000000000) := by
  have h := checkLog_sound (w := (6139 / 18939)) (n := 12)
    (lo := (168136449 / 250000000)) (hi := (672545797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12539 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12539 / 6400) = 1/(6400 / 12539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (168136449 / 250000000) (672545797 / 1000000000) (Real.log (12539 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12539 / 6400) = -Real.log (6400 / 12539) := by
    rw [show ((12539 / 6400) : ℝ) = ((6400 / 12539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3199532859 / 1000000000) ≤ -Real.log (261 / 6400) ∧
    -Real.log (261 / 6400) ≤ (49992701 / 15625000) := by
  have h := checkLog_sound (w := (139 / 661)) (n := 12)
    (lo := (426944139 / 1000000000)) (hi := (21347207 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 261) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 261) = 1/(261 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-49992701 / 15625000) (-3199532859 / 1000000000) (Real.log (261 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (672356369 / 1000000000) ≤ -Real.log (51200 / 100293) ∧
    -Real.log (51200 / 100293) ≤ (67235637 / 100000000) := by
  have h := checkLog_sound (w := (49093 / 151493)) (n := 12)
    (lo := (672356369 / 1000000000)) (hi := (67235637 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100293 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100293 / 51200) = 1/(51200 / 100293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (672356369 / 1000000000) (67235637 / 100000000) (Real.log (100293 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100293 / 51200) = -Real.log (51200 / 100293) := by
    rw [show ((100293 / 51200) : ℝ) = ((51200 / 100293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1595237197 / 500000000) ≤ -Real.log (2107 / 51200) ∧
    -Real.log (2107 / 51200) ≤ (3190474399 / 1000000000) := by
  have h := checkLog_sound (w := (1093 / 5307)) (n := 12)
    (lo := (208942837 / 500000000)) (hi := (16715427 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2107) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2107) = 1/(2107 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3190474399 / 1000000000) (-1595237197 / 500000000) (Real.log (2107 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (162877763 / 250000000) ≤ -Real.log (3200 / 6139) ∧
    -Real.log (3200 / 6139) ≤ (651511053 / 1000000000) := by
  have h := checkLog_sound (w := (2939 / 9339)) (n := 12)
    (lo := (162877763 / 250000000)) (hi := (651511053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6139 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6139 / 3200) = 1/(3200 / 6139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (162877763 / 250000000) (651511053 / 1000000000) (Real.log (6139 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (6139 / 3200) = -Real.log (3200 / 6139) := by
    rw [show ((6139 / 3200) : ℝ) = ((3200 / 6139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2506385679 / 1000000000) ≤ -Real.log (261 / 3200) ∧
    -Real.log (261 / 3200) ≤ (2506385683 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 661)) (n := 12)
    (lo := (426944139 / 1000000000)) (hi := (21347207 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 261) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 261) = 1/(261 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2506385683 / 1000000000) (-2506385679 / 1000000000) (Real.log (261 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (325562053 / 500000000) ≤ -Real.log (25600 / 49093) ∧
    -Real.log (25600 / 49093) ≤ (651124107 / 1000000000) := by
  have h := checkLog_sound (w := (23493 / 74693)) (n := 12)
    (lo := (325562053 / 500000000)) (hi := (651124107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49093 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49093 / 25600) = 1/(25600 / 49093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (325562053 / 500000000) (651124107 / 1000000000) (Real.log (49093 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49093 / 25600) = -Real.log (25600 / 49093) := by
    rw [show ((49093 / 25600) : ℝ) = ((25600 / 49093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1248663607 / 500000000) ≤ -Real.log (2107 / 25600) ∧
    -Real.log (2107 / 25600) ≤ (1248663609 / 500000000) := by
  have h := checkLog_sound (w := (1093 / 5307)) (n := 12)
    (lo := (208942837 / 500000000)) (hi := (16715427 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2107) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2107) = 1/(2107 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1248663609 / 500000000) (-1248663607 / 500000000) (Real.log (2107 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67608291 / 100000000) ≤ -Real.log (1000000 / 1966161) ∧
    -Real.log (1000000 / 1966161) ≤ (676082911 / 1000000000) := by
  have h := checkLog_sound (w := (966161 / 2966161)) (n := 12)
    (lo := (67608291 / 100000000)) (hi := (676082911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1966161 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1966161 / 1000000) = 1/(1000000 / 1966161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67608291 / 100000000) (676082911 / 1000000000) (Real.log (1966161 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1966161 / 1000000) = -Real.log (1000000 / 1966161) := by
    rw [show ((1966161 / 1000000) : ℝ) = ((1000000 / 1966161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3386141293 / 1000000000) ≤ -Real.log (33839 / 1000000) ∧
    -Real.log (33839 / 1000000) ≤ (1693070649 / 500000000) := by
  have h := checkLog_sound (w := (28661 / 96339)) (n := 12)
    (lo := (613552573 / 1000000000)) (hi := (306776287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33839) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 33839) = 1/(33839 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1693070649 / 500000000) (-3386141293 / 1000000000) (Real.log (33839 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (338114689 / 500000000) ≤ -Real.log (1000000 / 1966449) ∧
    -Real.log (1000000 / 1966449) ≤ (676229379 / 1000000000) := by
  have h := checkLog_sound (w := (966449 / 2966449)) (n := 12)
    (lo := (338114689 / 500000000)) (hi := (676229379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1966449 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1966449 / 1000000) = 1/(1000000 / 1966449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (338114689 / 500000000) (676229379 / 1000000000) (Real.log (1966449 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1966449 / 1000000) = -Real.log (1000000 / 1966449) := by
    rw [show ((1966449 / 1000000) : ℝ) = ((1000000 / 1966449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3394688607 / 1000000000) ≤ -Real.log (33551 / 1000000) ∧
    -Real.log (33551 / 1000000) ≤ (848672153 / 250000000) := by
  have h := checkLog_sound (w := (28949 / 96051)) (n := 12)
    (lo := (622099887 / 1000000000)) (hi := (38881243 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33551) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 33551) = 1/(33551 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-848672153 / 250000000) (-3394688607 / 1000000000) (Real.log (33551 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (675925739 / 1000000000) ≤ -Real.log (250000 / 491463) ∧
    -Real.log (250000 / 491463) ≤ (33796287 / 50000000) := by
  have h := checkLog_sound (w := (241463 / 741463)) (n := 12)
    (lo := (675925739 / 1000000000)) (hi := (33796287 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491463 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491463 / 250000) = 1/(250000 / 491463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (675925739 / 1000000000) (33796287 / 50000000) (Real.log (491463 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (491463 / 250000) = -Real.log (250000 / 491463) := by
    rw [show ((491463 / 250000) : ℝ) = ((250000 / 491463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3377051257 / 1000000000) ≤ -Real.log (8537 / 250000) ∧
    -Real.log (8537 / 250000) ≤ (1688525631 / 500000000) := by
  have h := checkLog_sound (w := (3544 / 12081)) (n := 12)
    (lo := (604462537 / 1000000000)) (hi := (302231269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8537) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8537) = 1/(8537 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1688525631 / 500000000) (-3377051257 / 1000000000) (Real.log (8537 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (67607579 / 100000000) ≤ -Real.log (1000000 / 1966147) ∧
    -Real.log (1000000 / 1966147) ≤ (676075791 / 1000000000) := by
  have h := checkLog_sound (w := (966147 / 2966147)) (n := 12)
    (lo := (67607579 / 100000000)) (hi := (676075791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1966147 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1966147 / 1000000) = 1/(1000000 / 1966147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (67607579 / 100000000) (676075791 / 1000000000) (Real.log (1966147 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1966147 / 1000000) = -Real.log (1000000 / 1966147) := by
    rw [show ((1966147 / 1000000) : ℝ) = ((1000000 / 1966147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (677145531 / 200000000) ≤ -Real.log (33853 / 1000000) ∧
    -Real.log (33853 / 1000000) ≤ (169286383 / 50000000) := by
  have h := checkLog_sound (w := (28647 / 96353)) (n := 12)
    (lo := (122627787 / 200000000)) (hi := (76642367 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33853) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 33853) = 1/(33853 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-169286383 / 50000000) (-677145531 / 200000000) (Real.log (33853 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4062224203 / 1000000000) ≤ -Real.log (4000000000 / 232413605603) ∧
    -Real.log (4000000000 / 232413605603) ≤ (4062224209 / 1000000000) := by
  have h := checkLog_sound (w := (104413605603 / 360413605603)) (n := 12)
    (lo := (596488303 / 1000000000)) (hi := (37280519 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232413605603 / 128000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(232413605603 / 128000000000) = 1/(4000000000 / 232413605603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4062224203 / 1000000000) (4062224209 / 1000000000) (Real.log (232413605603 / 4000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (232413605603 / 4000000000) = -Real.log (4000000000 / 232413605603) := by
    rw [show ((232413605603 / 4000000000) : ℝ) = ((4000000000 / 232413605603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (814183597 / 200000000) ≤ -Real.log (250000000000 / 14652685463921) ∧
    -Real.log (250000000000 / 14652685463921) ≤ (4070917991 / 1000000000) := by
  have h := checkLog_sound (w := (6652685463921 / 22652685463921)) (n := 12)
    (lo := (121036417 / 200000000)) (hi := (302591043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14652685463921 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(14652685463921 / 8000000000000) = 1/(250000000000 / 14652685463921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (814183597 / 200000000) (4070917991 / 1000000000) (Real.log (14652685463921 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14652685463921 / 250000000000) = -Real.log (250000000000 / 14652685463921) := by
    rw [show ((14652685463921 / 250000000000) : ℝ) = ((250000000000 / 14652685463921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1013244249 / 250000000) ≤ -Real.log (500000000000 / 28784291905821) ∧
    -Real.log (500000000000 / 28784291905821) ≤ (2026488501 / 500000000) := by
  have h := checkLog_sound (w := (12784291905821 / 44784291905821)) (n := 12)
    (lo := (73405137 / 125000000)) (hi := (587241097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28784291905821 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28784291905821 / 16000000000000) = 1/(500000000000 / 28784291905821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1013244249 / 250000000) (2026488501 / 500000000) (Real.log (28784291905821 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (28784291905821 / 500000000000) = -Real.log (500000000000 / 28784291905821) := by
    rw [show ((28784291905821 / 500000000000) : ℝ) = ((500000000000 / 28784291905821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1015450861 / 250000000) ≤ -Real.log (500000000000 / 29039479514371) ∧
    -Real.log (500000000000 / 29039479514371) ≤ (81236069 / 20000000) := by
  have h := checkLog_sound (w := (13039479514371 / 45039479514371)) (n := 12)
    (lo := (74508443 / 125000000)) (hi := (119213509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29039479514371 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(29039479514371 / 16000000000000) = 1/(500000000000 / 29039479514371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1015450861 / 250000000) (81236069 / 20000000) (Real.log (29039479514371 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (29039479514371 / 500000000000) = -Real.log (500000000000 / 29039479514371) := by
    rw [show ((29039479514371 / 500000000000) : ℝ) = ((500000000000 / 29039479514371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0094
