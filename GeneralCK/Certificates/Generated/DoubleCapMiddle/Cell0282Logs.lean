import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0282
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

theorem reflection_log_1_neg : (57032773 / 250000000) ≤ -Real.log (160 / 201) ∧
    -Real.log (160 / 201) ≤ (228131093 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 361)) (n := 12)
    (lo := (57032773 / 250000000)) (hi := (228131093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201 / 160) = 1/(160 / 201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (57032773 / 250000000) (228131093 / 1000000000) (Real.log (201 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201 / 160) = -Real.log (160 / 201) := by
    rw [show ((201 / 160) : ℝ) = ((160 / 201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (148025161 / 500000000) ≤ -Real.log (119 / 160) ∧
    -Real.log (119 / 160) ≤ (296050323 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 279)) (n := 12)
    (lo := (148025161 / 500000000)) (hi := (296050323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 119) = 1/(119 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-296050323 / 1000000000) (-148025161 / 500000000) (Real.log (119 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (445113 / 1953125) ≤ -Real.log (10240 / 12861) ∧
    -Real.log (10240 / 12861) ≤ (227897857 / 1000000000) := by
  have h := checkLog_sound (w := (2621 / 23101)) (n := 12)
    (lo := (445113 / 1953125)) (hi := (227897857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12861 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12861 / 10240) = 1/(10240 / 12861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (445113 / 1953125) (227897857 / 1000000000) (Real.log (12861 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12861 / 10240) = -Real.log (10240 / 12861) := by
    rw [show ((12861 / 10240) : ℝ) = ((10240 / 12861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (73914123 / 250000000) ≤ -Real.log (7619 / 10240) ∧
    -Real.log (7619 / 10240) ≤ (295656493 / 1000000000) := by
  have h := checkLog_sound (w := (2621 / 17859)) (n := 12)
    (lo := (73914123 / 250000000)) (hi := (295656493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7619) = 1/(7619 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-295656493 / 1000000000) (-73914123 / 250000000) (Real.log (7619 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (41376391 / 100000000) ≤ -Real.log (80 / 121) ∧
    -Real.log (80 / 121) ≤ (413763911 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 201)) (n := 12)
    (lo := (41376391 / 100000000)) (hi := (413763911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121 / 80) = 1/(80 / 121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (41376391 / 100000000) (413763911 / 1000000000) (Real.log (121 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (121 / 80) = -Real.log (80 / 121) := by
    rw [show ((121 / 80) : ℝ) = ((80 / 121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (718464987 / 1000000000) ≤ -Real.log (39 / 80) ∧
    -Real.log (39 / 80) ≤ (718464989 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 39) = 1/(39 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-718464989 / 1000000000) (-718464987 / 1000000000) (Real.log (39 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (413376439 / 1000000000) ≤ -Real.log (5120 / 7741) ∧
    -Real.log (5120 / 7741) ≤ (10334411 / 25000000) := by
  have h := checkLog_sound (w := (2621 / 12861)) (n := 12)
    (lo := (413376439 / 1000000000)) (hi := (10334411 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7741 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7741 / 5120) = 1/(5120 / 7741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (413376439 / 1000000000) (10334411 / 25000000) (Real.log (7741 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7741 / 5120) = -Real.log (5120 / 7741) := by
    rw [show ((7741 / 5120) : ℝ) = ((5120 / 7741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (358631893 / 500000000) ≤ -Real.log (2499 / 5120) ∧
    -Real.log (2499 / 5120) ≤ (179315947 / 250000000) := by
  have h := checkLog_sound (w := (61 / 5059)) (n := 12)
    (lo := (12058303 / 500000000)) (hi := (24116607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2499) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2499) = 1/(2499 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-179315947 / 250000000) (-358631893 / 500000000) (Real.log (2499 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (156101481 / 500000000) ≤ -Real.log (31250 / 42701) ∧
    -Real.log (31250 / 42701) ≤ (312202963 / 1000000000) := by
  have h := checkLog_sound (w := (11451 / 73951)) (n := 12)
    (lo := (156101481 / 500000000)) (hi := (312202963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42701 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42701 / 31250) = 1/(31250 / 42701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (156101481 / 500000000) (312202963 / 1000000000) (Real.log (42701 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (42701 / 31250) = -Real.log (31250 / 42701) := by
    rw [show ((42701 / 31250) : ℝ) = ((31250 / 42701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (57048493 / 125000000) ≤ -Real.log (19799 / 31250) ∧
    -Real.log (19799 / 31250) ≤ (91277589 / 200000000) := by
  have h := checkLog_sound (w := (11451 / 51049)) (n := 12)
    (lo := (57048493 / 125000000)) (hi := (91277589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 19799) = 1/(19799 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-91277589 / 200000000) (-57048493 / 125000000) (Real.log (19799 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (39064883 / 125000000) ≤ -Real.log (62500 / 85429) ∧
    -Real.log (62500 / 85429) ≤ (62503813 / 200000000) := by
  have h := checkLog_sound (w := (22929 / 147929)) (n := 12)
    (lo := (39064883 / 125000000)) (hi := (62503813 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85429 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85429 / 62500) = 1/(62500 / 85429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (39064883 / 125000000) (62503813 / 200000000) (Real.log (85429 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (85429 / 62500) = -Real.log (62500 / 85429) := by
    rw [show ((85429 / 62500) : ℝ) = ((62500 / 85429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (457070029 / 1000000000) ≤ -Real.log (39571 / 62500) ∧
    -Real.log (39571 / 62500) ≤ (45707003 / 100000000) := by
  have h := checkLog_sound (w := (22929 / 102071)) (n := 12)
    (lo := (457070029 / 1000000000)) (hi := (45707003 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 39571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 39571) = 1/(39571 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-45707003 / 100000000) (-457070029 / 1000000000) (Real.log (39571 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (9532351 / 40000000) ≤ -Real.log (1000000 / 1269101) ∧
    -Real.log (1000000 / 1269101) ≤ (29788597 / 125000000) := by
  have h := checkLog_sound (w := (269101 / 2269101)) (n := 12)
    (lo := (9532351 / 40000000)) (hi := (29788597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269101 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1269101 / 1000000) = 1/(1000000 / 1269101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (9532351 / 40000000) (29788597 / 125000000) (Real.log (1269101 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1269101 / 1000000) = -Real.log (1000000 / 1269101) := by
    rw [show ((1269101 / 1000000) : ℝ) = ((1000000 / 1269101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (62695999 / 200000000) ≤ -Real.log (730899 / 1000000) ∧
    -Real.log (730899 / 1000000) ≤ (78369999 / 250000000) := by
  have h := checkLog_sound (w := (269101 / 1730899)) (n := 12)
    (lo := (62695999 / 200000000)) (hi := (78369999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 730899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 730899) = 1/(730899 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-78369999 / 250000000) (-62695999 / 200000000) (Real.log (730899 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (238578221 / 1000000000) ≤ -Real.log (1000000 / 1269443) ∧
    -Real.log (1000000 / 1269443) ≤ (119289111 / 500000000) := by
  have h := checkLog_sound (w := (269443 / 2269443)) (n := 12)
    (lo := (238578221 / 1000000000)) (hi := (119289111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269443 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1269443 / 1000000) = 1/(1000000 / 1269443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (238578221 / 1000000000) (119289111 / 500000000) (Real.log (1269443 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1269443 / 1000000) = -Real.log (1000000 / 1269443) := by
    rw [show ((1269443 / 1000000) : ℝ) = ((1000000 / 1269443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (156974011 / 500000000) ≤ -Real.log (730557 / 1000000) ∧
    -Real.log (730557 / 1000000) ≤ (313948023 / 1000000000) := by
  have h := checkLog_sound (w := (269443 / 1730557)) (n := 12)
    (lo := (156974011 / 500000000)) (hi := (313948023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 730557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 730557) = 1/(730557 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-313948023 / 1000000000) (-156974011 / 500000000) (Real.log (730557 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (768590907 / 1000000000) ≤ -Real.log (250000000000 / 539181271781) ∧
    -Real.log (250000000000 / 539181271781) ≤ (768590909 / 1000000000) := by
  have h := checkLog_sound (w := (39181271781 / 1039181271781)) (n := 12)
    (lo := (75443727 / 1000000000)) (hi := (4715233 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539181271781 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(539181271781 / 500000000000) = 1/(250000000000 / 539181271781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (768590907 / 1000000000) (768590909 / 1000000000) (Real.log (539181271781 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (539181271781 / 250000000000) = -Real.log (250000000000 / 539181271781) := by
    rw [show ((539181271781 / 250000000000) : ℝ) = ((250000000000 / 539181271781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (384794547 / 500000000) ≤ -Real.log (100000000000 / 215887897703) ∧
    -Real.log (100000000000 / 215887897703) ≤ (96198637 / 125000000) := by
  have h := checkLog_sound (w := (15887897703 / 415887897703)) (n := 12)
    (lo := (38220957 / 500000000)) (hi := (15288383 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215887897703 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(215887897703 / 200000000000) = 1/(100000000000 / 215887897703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (384794547 / 500000000) (96198637 / 125000000) (Real.log (215887897703 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (215887897703 / 100000000000) = -Real.log (100000000000 / 215887897703) := by
    rw [show ((215887897703 / 100000000000) : ℝ) = ((100000000000 / 215887897703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (551788771 / 1000000000) ≤ -Real.log (250000000000 / 434089046503) ∧
    -Real.log (250000000000 / 434089046503) ≤ (137947193 / 250000000) := by
  have h := checkLog_sound (w := (184089046503 / 684089046503)) (n := 12)
    (lo := (551788771 / 1000000000)) (hi := (137947193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((434089046503 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(434089046503 / 250000000000) = 1/(250000000000 / 434089046503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (551788771 / 1000000000) (137947193 / 250000000) (Real.log (434089046503 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (434089046503 / 250000000000) = -Real.log (250000000000 / 434089046503) := by
    rw [show ((434089046503 / 250000000000) : ℝ) = ((250000000000 / 434089046503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (552526243 / 1000000000) ≤ -Real.log (500000000000 / 868818586367) ∧
    -Real.log (500000000000 / 868818586367) ≤ (138131561 / 250000000) := by
  have h := checkLog_sound (w := (368818586367 / 1368818586367)) (n := 12)
    (lo := (552526243 / 1000000000)) (hi := (138131561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((868818586367 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(868818586367 / 500000000000) = 1/(500000000000 / 868818586367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (552526243 / 1000000000) (138131561 / 250000000) (Real.log (868818586367 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (868818586367 / 500000000000) = -Real.log (500000000000 / 868818586367) := by
    rw [show ((868818586367 / 500000000000) : ℝ) = ((500000000000 / 868818586367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0282
