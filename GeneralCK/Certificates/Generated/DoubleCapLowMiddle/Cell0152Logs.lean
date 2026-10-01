import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0152
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

theorem reflection_log_1_neg : (325938747 / 500000000) ≤ -Real.log (2560 / 4913) ∧
    -Real.log (2560 / 4913) ≤ (130375499 / 200000000) := by
  have h := checkLog_sound (w := (2353 / 7473)) (n := 12)
    (lo := (325938747 / 500000000)) (hi := (130375499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4913 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4913 / 2560) = 1/(2560 / 4913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (325938747 / 500000000) (130375499 / 200000000) (Real.log (4913 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (4913 / 2560) = -Real.log (2560 / 4913) := by
    rw [show ((4913 / 2560) : ℝ) = ((2560 / 4913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1257521871 / 500000000) ≤ -Real.log (207 / 2560) ∧
    -Real.log (207 / 2560) ≤ (1257521873 / 500000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 207) = 1/(207 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1257521873 / 500000000) (-1257521871 / 500000000) (Real.log (207 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (651103737 / 1000000000) ≤ -Real.log (6400 / 12273) ∧
    -Real.log (6400 / 12273) ≤ (325551869 / 500000000) := by
  have h := checkLog_sound (w := (5873 / 18673)) (n := 12)
    (lo := (651103737 / 1000000000)) (hi := (325551869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12273 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12273 / 6400) = 1/(6400 / 12273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (651103737 / 1000000000) (325551869 / 500000000) (Real.log (12273 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12273 / 6400) = -Real.log (6400 / 12273) := by
    rw [show ((12273 / 6400) : ℝ) = ((6400 / 12273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2496852719 / 1000000000) ≤ -Real.log (527 / 6400) ∧
    -Real.log (527 / 6400) ≤ (2496852723 / 1000000000) := by
  have h := checkLog_sound (w := (273 / 1327)) (n := 12)
    (lo := (417411179 / 1000000000)) (hi := (20870559 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 527) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 527) = 1/(527 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2496852723 / 1000000000) (-2496852719 / 1000000000) (Real.log (527 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (608831031 / 1000000000) ≤ -Real.log (1280 / 2353) ∧
    -Real.log (1280 / 2353) ≤ (76103879 / 125000000) := by
  have h := checkLog_sound (w := (1073 / 3633)) (n := 12)
    (lo := (608831031 / 1000000000)) (hi := (76103879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2353 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2353 / 1280) = 1/(1280 / 2353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (608831031 / 1000000000) (76103879 / 125000000) (Real.log (2353 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2353 / 1280) = -Real.log (1280 / 2353) := by
    rw [show ((2353 / 1280) : ℝ) = ((1280 / 2353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (910948281 / 500000000) ≤ -Real.log (207 / 1280) ∧
    -Real.log (207 / 1280) ≤ (364379313 / 200000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 207) = 1/(207 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-364379313 / 200000000) (-910948281 / 500000000) (Real.log (207 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (303607383 / 500000000) ≤ -Real.log (3200 / 5873) ∧
    -Real.log (3200 / 5873) ≤ (607214767 / 1000000000) := by
  have h := checkLog_sound (w := (2673 / 9073)) (n := 12)
    (lo := (303607383 / 500000000)) (hi := (607214767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5873 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5873 / 3200) = 1/(3200 / 5873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (303607383 / 500000000) (607214767 / 1000000000) (Real.log (5873 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5873 / 3200) = -Real.log (3200 / 5873) := by
    rw [show ((5873 / 3200) : ℝ) = ((3200 / 5873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1803705539 / 1000000000) ≤ -Real.log (527 / 3200) ∧
    -Real.log (527 / 3200) ≤ (901852771 / 500000000) := by
  have h := checkLog_sound (w := (273 / 1327)) (n := 12)
    (lo := (417411179 / 1000000000)) (hi := (20870559 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 527) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 527) = 1/(527 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-901852771 / 500000000) (-1803705539 / 1000000000) (Real.log (527 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (660441637 / 1000000000) ≤ -Real.log (1000000 / 1935647) ∧
    -Real.log (1000000 / 1935647) ≤ (330220819 / 500000000) := by
  have h := checkLog_sound (w := (935647 / 2935647)) (n := 12)
    (lo := (660441637 / 1000000000)) (hi := (330220819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1935647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1935647 / 1000000) = 1/(1000000 / 1935647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (660441637 / 1000000000) (330220819 / 500000000) (Real.log (1935647 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1935647 / 1000000) = -Real.log (1000000 / 1935647) := by
    rw [show ((1935647 / 1000000) : ℝ) = ((1000000 / 1935647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (685842931 / 250000000) ≤ -Real.log (64353 / 1000000) ∧
    -Real.log (64353 / 1000000) ≤ (171460733 / 62500000) := by
  have h := checkLog_sound (w := (60647 / 189353)) (n := 12)
    (lo := (82991273 / 125000000)) (hi := (132786037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 64353) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 64353) = 1/(64353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-171460733 / 62500000) (-685842931 / 250000000) (Real.log (64353 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (66098601 / 100000000) ≤ -Real.log (1000000 / 1936701) ∧
    -Real.log (1000000 / 1936701) ≤ (660986011 / 1000000000) := by
  have h := checkLog_sound (w := (936701 / 2936701)) (n := 12)
    (lo := (66098601 / 100000000)) (hi := (660986011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1936701 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1936701 / 1000000) = 1/(1000000 / 1936701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (66098601 / 100000000) (660986011 / 1000000000) (Real.log (1936701 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1936701 / 1000000) = -Real.log (1000000 / 1936701) := by
    rw [show ((1936701 / 1000000) : ℝ) = ((1000000 / 1936701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1379942873 / 500000000) ≤ -Real.log (63299 / 1000000) ∧
    -Real.log (63299 / 1000000) ≤ (11039543 / 4000000) := by
  have h := checkLog_sound (w := (61701 / 188299)) (n := 12)
    (lo := (340222103 / 500000000)) (hi := (680444207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 63299) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 63299) = 1/(63299 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-11039543 / 4000000) (-1379942873 / 500000000) (Real.log (63299 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (659662783 / 1000000000) ≤ -Real.log (50000 / 96707) ∧
    -Real.log (50000 / 96707) ≤ (10307231 / 15625000) := by
  have h := checkLog_sound (w := (46707 / 146707)) (n := 12)
    (lo := (659662783 / 1000000000)) (hi := (10307231 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96707 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96707 / 50000) = 1/(50000 / 96707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (659662783 / 1000000000) (10307231 / 15625000) (Real.log (96707 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (96707 / 50000) = -Real.log (50000 / 96707) := by
    rw [show ((96707 / 50000) : ℝ) = ((50000 / 96707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (85007 / 31250) ≤ -Real.log (3293 / 50000) ∧
    -Real.log (3293 / 50000) ≤ (680056001 / 250000000) := by
  have h := checkLog_sound (w := (2957 / 9543)) (n := 12)
    (lo := (32039123 / 50000000)) (hi := (640782461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3293) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6250 / 3293) = 1/(3293 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-680056001 / 250000000) (-85007 / 31250) (Real.log (3293 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (660239617 / 1000000000) ≤ -Real.log (125000 / 241907) ∧
    -Real.log (125000 / 241907) ≤ (330119809 / 500000000) := by
  have h := checkLog_sound (w := (116907 / 366907)) (n := 12)
    (lo := (660239617 / 1000000000)) (hi := (330119809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241907 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241907 / 125000) = 1/(125000 / 241907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (660239617 / 1000000000) (330119809 / 500000000) (Real.log (241907 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (241907 / 125000) = -Real.log (125000 / 241907) := by
    rw [show ((241907 / 125000) : ℝ) = ((125000 / 241907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (547462849 / 200000000) ≤ -Real.log (8093 / 125000) ∧
    -Real.log (8093 / 125000) ≤ (2737314249 / 1000000000) := by
  have h := checkLog_sound (w := (3766 / 11859)) (n := 12)
    (lo := (131574541 / 200000000)) (hi := (328936353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8093) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 8093) = 1/(8093 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2737314249 / 1000000000) (-547462849 / 200000000) (Real.log (8093 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3403813361 / 1000000000) ≤ -Real.log (25000000000 / 751964554877) ∧
    -Real.log (25000000000 / 751964554877) ≤ (1701906683 / 500000000) := by
  have h := checkLog_sound (w := (351964554877 / 1151964554877)) (n := 12)
    (lo := (631224641 / 1000000000)) (hi := (315612321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751964554877 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(751964554877 / 400000000000) = 1/(25000000000 / 751964554877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3403813361 / 1000000000) (1701906683 / 500000000) (Real.log (751964554877 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (751964554877 / 25000000000) = -Real.log (25000000000 / 751964554877) := by
    rw [show ((751964554877 / 25000000000) : ℝ) = ((25000000000 / 751964554877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (684174351 / 200000000) ≤ -Real.log (100000000000 / 3059607576739) ∧
    -Real.log (100000000000 / 3059607576739) ≤ (42760897 / 12500000) := by
  have h := checkLog_sound (w := (1459607576739 / 4659607576739)) (n := 12)
    (lo := (129656607 / 200000000)) (hi := (162070759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3059607576739 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3059607576739 / 1600000000000) = 1/(100000000000 / 3059607576739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (684174351 / 200000000) (42760897 / 12500000) (Real.log (3059607576739 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3059607576739 / 100000000000) = -Real.log (100000000000 / 3059607576739) := by
    rw [show ((3059607576739 / 100000000000) : ℝ) = ((100000000000 / 3059607576739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3379886783 / 1000000000) ≤ -Real.log (500000000000 / 14683723048891) ∧
    -Real.log (500000000000 / 14683723048891) ≤ (844971697 / 250000000) := by
  have h := checkLog_sound (w := (6683723048891 / 22683723048891)) (n := 12)
    (lo := (607298063 / 1000000000)) (hi := (37956129 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14683723048891 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(14683723048891 / 8000000000000) = 1/(500000000000 / 14683723048891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3379886783 / 1000000000) (844971697 / 250000000) (Real.log (14683723048891 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (14683723048891 / 500000000000) = -Real.log (500000000000 / 14683723048891) := by
    rw [show ((14683723048891 / 500000000000) : ℝ) = ((500000000000 / 14683723048891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1698776931 / 500000000) ≤ -Real.log (500000000000 / 14945446682319) ∧
    -Real.log (500000000000 / 14945446682319) ≤ (3397553867 / 1000000000) := by
  have h := checkLog_sound (w := (6945446682319 / 22945446682319)) (n := 12)
    (lo := (312482571 / 500000000)) (hi := (624965143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14945446682319 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(14945446682319 / 8000000000000) = 1/(500000000000 / 14945446682319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1698776931 / 500000000) (3397553867 / 1000000000) (Real.log (14945446682319 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (14945446682319 / 500000000000) = -Real.log (500000000000 / 14945446682319) := by
    rw [show ((14945446682319 / 500000000000) : ℝ) = ((500000000000 / 14945446682319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0152
