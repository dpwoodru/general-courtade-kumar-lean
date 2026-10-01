import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0187
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

theorem reflection_log_1_neg : (2401749 / 3906250) ≤ -Real.log (1600 / 2959) ∧
    -Real.log (1600 / 2959) ≤ (122969549 / 200000000) := by
  have h := checkLog_sound (w := (1359 / 4559)) (n := 12)
    (lo := (2401749 / 3906250)) (hi := (122969549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2959 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2959 / 1600) = 1/(1600 / 2959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (2401749 / 3906250) (122969549 / 200000000) (Real.log (2959 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2959 / 1600) = -Real.log (1600 / 2959) := by
    rw [show ((2959 / 1600) : ℝ) = ((1600 / 2959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1892961973 / 1000000000) ≤ -Real.log (241 / 1600) ∧
    -Real.log (241 / 1600) ≤ (236620247 / 125000000) := by
  have h := checkLog_sound (w := (159 / 641)) (n := 12)
    (lo := (506667613 / 1000000000)) (hi := (253333807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 241) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 241) = 1/(241 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-236620247 / 125000000) (-1892961973 / 1000000000) (Real.log (241 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (306620591 / 500000000) ≤ -Real.log (6400 / 11817) ∧
    -Real.log (6400 / 11817) ≤ (613241183 / 1000000000) := by
  have h := checkLog_sound (w := (5417 / 18217)) (n := 12)
    (lo := (306620591 / 500000000)) (hi := (613241183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11817 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11817 / 6400) = 1/(6400 / 11817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (306620591 / 500000000) (613241183 / 1000000000) (Real.log (11817 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11817 / 6400) = -Real.log (6400 / 11817) := by
    rw [show ((11817 / 6400) : ℝ) = ((6400 / 11817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (468361037 / 250000000) ≤ -Real.log (983 / 6400) ∧
    -Real.log (983 / 6400) ≤ (1873444151 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 2583)) (n := 12)
    (lo := (121787447 / 250000000)) (hi := (487149789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 983) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 983) = 1/(983 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1873444151 / 1000000000) (-468361037 / 250000000) (Real.log (983 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (264946343 / 500000000) ≤ -Real.log (800 / 1359) ∧
    -Real.log (800 / 1359) ≤ (529892687 / 1000000000) := by
  have h := checkLog_sound (w := (559 / 2159)) (n := 12)
    (lo := (264946343 / 500000000)) (hi := (529892687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359 / 800) = 1/(800 / 1359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (264946343 / 500000000) (529892687 / 1000000000) (Real.log (1359 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1359 / 800) = -Real.log (800 / 1359) := by
    rw [show ((1359 / 800) : ℝ) = ((800 / 1359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1199814793 / 1000000000) ≤ -Real.log (241 / 800) ∧
    -Real.log (241 / 800) ≤ (239962959 / 200000000) := by
  have h := checkLog_sound (w := (159 / 641)) (n := 12)
    (lo := (506667613 / 1000000000)) (hi := (253333807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 241) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 241) = 1/(241 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-239962959 / 200000000) (-1199814793 / 1000000000) (Real.log (241 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (263195673 / 500000000) ≤ -Real.log (3200 / 5417) ∧
    -Real.log (3200 / 5417) ≤ (526391347 / 1000000000) := by
  have h := checkLog_sound (w := (2217 / 8617)) (n := 12)
    (lo := (263195673 / 500000000)) (hi := (526391347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5417 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5417 / 3200) = 1/(3200 / 5417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (263195673 / 500000000) (526391347 / 1000000000) (Real.log (5417 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5417 / 3200) = -Real.log (3200 / 5417) := by
    rw [show ((5417 / 3200) : ℝ) = ((3200 / 5417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (147537121 / 125000000) ≤ -Real.log (983 / 3200) ∧
    -Real.log (983 / 3200) ≤ (118029697 / 100000000) := by
  have h := checkLog_sound (w := (617 / 2583)) (n := 12)
    (lo := (121787447 / 250000000)) (hi := (487149789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 983) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 983) = 1/(983 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-118029697 / 100000000) (-147537121 / 125000000) (Real.log (983 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (79503831 / 125000000) ≤ -Real.log (125000 / 236121) ∧
    -Real.log (125000 / 236121) ≤ (636030649 / 1000000000) := by
  have h := checkLog_sound (w := (111121 / 361121)) (n := 12)
    (lo := (79503831 / 125000000)) (hi := (636030649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236121 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236121 / 125000) = 1/(125000 / 236121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (79503831 / 125000000) (636030649 / 1000000000) (Real.log (236121 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (236121 / 125000) = -Real.log (125000 / 236121) := by
    rw [show ((236121 / 125000) : ℝ) = ((125000 / 236121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2197936829 / 1000000000) ≤ -Real.log (13879 / 125000) ∧
    -Real.log (13879 / 125000) ≤ (2197936833 / 1000000000) := by
  have h := checkLog_sound (w := (873 / 14752)) (n := 12)
    (lo := (118495289 / 1000000000)) (hi := (11849529 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13879) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 13879) = 1/(13879 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2197936833 / 1000000000) (-2197936829 / 1000000000) (Real.log (13879 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31849049 / 50000000) ≤ -Real.log (250000 / 472691) ∧
    -Real.log (250000 / 472691) ≤ (636980981 / 1000000000) := by
  have h := checkLog_sound (w := (222691 / 722691)) (n := 12)
    (lo := (31849049 / 50000000)) (hi := (636980981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((472691 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(472691 / 250000) = 1/(250000 / 472691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31849049 / 50000000) (636980981 / 1000000000) (Real.log (472691 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (472691 / 250000) = -Real.log (250000 / 472691) := by
    rw [show ((472691 / 250000) : ℝ) = ((250000 / 472691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2214244597 / 1000000000) ≤ -Real.log (27309 / 250000) ∧
    -Real.log (27309 / 250000) ≤ (2214244601 / 1000000000) := by
  have h := checkLog_sound (w := (3941 / 58559)) (n := 12)
    (lo := (134803057 / 1000000000)) (hi := (67401529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27309) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 27309) = 1/(27309 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2214244601 / 1000000000) (-2214244597 / 1000000000) (Real.log (27309 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (632575713 / 1000000000) ≤ -Real.log (1000000 / 1882453) ∧
    -Real.log (1000000 / 1882453) ≤ (316287857 / 500000000) := by
  have h := checkLog_sound (w := (882453 / 2882453)) (n := 12)
    (lo := (632575713 / 1000000000)) (hi := (316287857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1882453 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1882453 / 1000000) = 1/(1000000 / 1882453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (632575713 / 1000000000) (316287857 / 500000000) (Real.log (1882453 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1882453 / 1000000) = -Real.log (1000000 / 1882453) := by
    rw [show ((1882453 / 1000000) : ℝ) = ((1000000 / 1882453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2140917023 / 1000000000) ≤ -Real.log (117547 / 1000000) ∧
    -Real.log (117547 / 1000000) ≤ (2140917027 / 1000000000) := by
  have h := checkLog_sound (w := (7453 / 242547)) (n := 12)
    (lo := (61475483 / 1000000000)) (hi := (15368871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 117547) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 117547) = 1/(117547 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2140917027 / 1000000000) (-2140917023 / 1000000000) (Real.log (117547 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (158421603 / 250000000) ≤ -Real.log (200000 / 376909) ∧
    -Real.log (200000 / 376909) ≤ (633686413 / 1000000000) := by
  have h := checkLog_sound (w := (176909 / 576909)) (n := 12)
    (lo := (158421603 / 250000000)) (hi := (633686413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376909 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376909 / 200000) = 1/(200000 / 376909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (158421603 / 250000000) (633686413 / 1000000000) (Real.log (376909 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (376909 / 200000) = -Real.log (200000 / 376909) := by
    rw [show ((376909 / 200000) : ℝ) = ((200000 / 376909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2158874433 / 1000000000) ≤ -Real.log (23091 / 200000) ∧
    -Real.log (23091 / 200000) ≤ (2158874437 / 1000000000) := by
  have h := checkLog_sound (w := (1909 / 48091)) (n := 12)
    (lo := (79432893 / 1000000000)) (hi := (39716447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 23091) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 23091) = 1/(23091 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2158874437 / 1000000000) (-2158874433 / 1000000000) (Real.log (23091 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (708491869 / 250000000) ≤ -Real.log (250000000000 / 4253206282873) ∧
    -Real.log (250000000000 / 4253206282873) ≤ (2833967481 / 1000000000) := by
  have h := checkLog_sound (w := (253206282873 / 8253206282873)) (n := 12)
    (lo := (15344689 / 250000000)) (hi := (61378757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4253206282873 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4253206282873 / 4000000000000) = 1/(250000000000 / 4253206282873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (708491869 / 250000000) (2833967481 / 1000000000) (Real.log (4253206282873 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4253206282873 / 250000000000) = -Real.log (250000000000 / 4253206282873) := by
    rw [show ((4253206282873 / 250000000000) : ℝ) = ((250000000000 / 4253206282873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2851225577 / 1000000000) ≤ -Real.log (25000000000 / 432724559669) ∧
    -Real.log (25000000000 / 432724559669) ≤ (1425612791 / 500000000) := by
  have h := checkLog_sound (w := (32724559669 / 832724559669)) (n := 12)
    (lo := (78636857 / 1000000000)) (hi := (39318429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432724559669 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(432724559669 / 400000000000) = 1/(25000000000 / 432724559669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2851225577 / 1000000000) (1425612791 / 500000000) (Real.log (432724559669 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (432724559669 / 25000000000) = -Real.log (25000000000 / 432724559669) := by
    rw [show ((432724559669 / 25000000000) : ℝ) = ((25000000000 / 432724559669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5416978 / 1953125) ≤ -Real.log (50000000000 / 800723540371) ∧
    -Real.log (50000000000 / 800723540371) ≤ (2773492741 / 1000000000) := by
  have h := checkLog_sound (w := (723540371 / 1600723540371)) (n := 12)
    (lo := (56501 / 62500000)) (hi := (904017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800723540371 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800723540371 / 800000000000) = 1/(50000000000 / 800723540371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (5416978 / 1953125) (2773492741 / 1000000000) (Real.log (800723540371 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (800723540371 / 50000000000) = -Real.log (50000000000 / 800723540371) := by
    rw [show ((800723540371 / 50000000000) : ℝ) = ((50000000000 / 800723540371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (558512169 / 200000000) ≤ -Real.log (500000000000 / 8161383222901) ∧
    -Real.log (500000000000 / 8161383222901) ≤ (55851217 / 20000000) := by
  have h := checkLog_sound (w := (161383222901 / 16161383222901)) (n := 12)
    (lo := (159777 / 8000000)) (hi := (9986063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8161383222901 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8161383222901 / 8000000000000) = 1/(500000000000 / 8161383222901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (558512169 / 200000000) (55851217 / 20000000) (Real.log (8161383222901 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (8161383222901 / 500000000000) = -Real.log (500000000000 / 8161383222901) := by
    rw [show ((8161383222901 / 500000000000) : ℝ) = ((500000000000 / 8161383222901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0187
