import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0008
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

theorem reflection_log_1_neg : (41376391 / 100000000) ≤ -Real.log (80 / 121) ∧
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


theorem reflection_log_1 : Bounds (41376391 / 100000000) (413763911 / 1000000000) (Real.log (121 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (121 / 80) = -Real.log (80 / 121) := by
    rw [show ((121 / 80) : ℝ) = ((80 / 121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (718464987 / 1000000000) ≤ -Real.log (39 / 80) ∧
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


theorem reflection_log_2 : Bounds (-718464989 / 1000000000) (-718464987 / 1000000000) (Real.log (39 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (204811559 / 500000000) ≤ -Real.log (160 / 241) ∧
    -Real.log (160 / 241) ≤ (409623119 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 401)) (n := 12)
    (lo := (204811559 / 500000000)) (hi := (409623119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241 / 160) = 1/(160 / 241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (204811559 / 500000000) (409623119 / 1000000000) (Real.log (241 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (241 / 160) = -Real.log (160 / 241) := by
    rw [show ((241 / 160) : ℝ) = ((160 / 241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (352862981 / 500000000) ≤ -Real.log (79 / 160) ∧
    -Real.log (79 / 160) ≤ (176431491 / 250000000) := by
  have h := checkLog_sound (w := (1 / 159)) (n := 12)
    (lo := (6289391 / 500000000)) (hi := (12578783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 79) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 79) = 1/(79 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-176431491 / 250000000) (-352862981 / 500000000) (Real.log (79 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (6173153 / 250000000) ≤ -Real.log (40 / 41) ∧
    -Real.log (40 / 41) ≤ (24692613 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 81)) (n := 12)
    (lo := (6173153 / 250000000)) (hi := (24692613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41 / 40) = 1/(40 / 41) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (6173153 / 250000000) (24692613 / 1000000000) (Real.log (41 / 40)) := by
  have h := reflection_log_5_neg
  have he : Real.log (41 / 40) = -Real.log (40 / 41) := by
    rw [show ((41 / 40) : ℝ) = ((40 / 41) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (25317807 / 1000000000) ≤ -Real.log (39 / 40) ∧
    -Real.log (39 / 40) ≤ (1582363 / 62500000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 39) = 1/(39 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1582363 / 62500000) (-25317807 / 1000000000) (Real.log (39 / 40)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (12422519 / 1000000000) ≤ -Real.log (80 / 81) ∧
    -Real.log (80 / 81) ≤ (310563 / 25000000) := by
  have h := checkLog_sound (w := (1 / 161)) (n := 12)
    (lo := (12422519 / 1000000000)) (hi := (310563 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81 / 80) = 1/(80 / 81) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (12422519 / 1000000000) (310563 / 25000000) (Real.log (81 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (81 / 80) = -Real.log (80 / 81) := by
    rw [show ((81 / 80) : ℝ) = ((80 / 81) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6289391 / 500000000) ≤ -Real.log (79 / 80) ∧
    -Real.log (79 / 80) ≤ (12578783 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 159)) (n := 12)
    (lo := (6289391 / 500000000)) (hi := (12578783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 79) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 79) = 1/(79 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12578783 / 1000000000) (-6289391 / 500000000) (Real.log (79 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (57660269 / 100000000) ≤ -Real.log (1000000 / 1779981) ∧
    -Real.log (1000000 / 1779981) ≤ (576602691 / 1000000000) := by
  have h := checkLog_sound (w := (779981 / 2779981)) (n := 12)
    (lo := (57660269 / 100000000)) (hi := (576602691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1779981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1779981 / 1000000) = 1/(1000000 / 1779981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (57660269 / 100000000) (576602691 / 1000000000) (Real.log (1779981 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1779981 / 1000000) = -Real.log (1000000 / 1779981) := by
    rw [show ((1779981 / 1000000) : ℝ) = ((1000000 / 1779981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1514041371 / 1000000000) ≤ -Real.log (220019 / 1000000) ∧
    -Real.log (220019 / 1000000) ≤ (757020687 / 500000000) := by
  have h := checkLog_sound (w := (29981 / 470019)) (n := 12)
    (lo := (127747011 / 1000000000)) (hi := (31936753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 220019) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 220019) = 1/(220019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-757020687 / 500000000) (-1514041371 / 1000000000) (Real.log (220019 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (576666171 / 1000000000) ≤ -Real.log (500000 / 890047) ∧
    -Real.log (500000 / 890047) ≤ (144166543 / 250000000) := by
  have h := checkLog_sound (w := (390047 / 1390047)) (n := 12)
    (lo := (576666171 / 1000000000)) (hi := (144166543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((890047 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(890047 / 500000) = 1/(500000 / 890047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (576666171 / 1000000000) (144166543 / 250000000) (Real.log (890047 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (890047 / 500000) = -Real.log (500000 / 890047) := by
    rw [show ((890047 / 500000) : ℝ) = ((500000 / 890047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (302911019 / 200000000) ≤ -Real.log (109953 / 500000) ∧
    -Real.log (109953 / 500000) ≤ (757277549 / 500000000) := by
  have h := checkLog_sound (w := (15047 / 234953)) (n := 12)
    (lo := (25652147 / 200000000)) (hi := (1002037 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 109953) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 109953) = 1/(109953 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-757277549 / 500000000) (-302911019 / 200000000) (Real.log (109953 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (508487893 / 1000000000) ≤ -Real.log (40000 / 66511) ∧
    -Real.log (40000 / 66511) ≤ (254243947 / 500000000) := by
  have h := checkLog_sound (w := (26511 / 106511)) (n := 12)
    (lo := (508487893 / 1000000000)) (hi := (254243947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66511 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66511 / 40000) = 1/(40000 / 66511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (508487893 / 1000000000) (254243947 / 500000000) (Real.log (66511 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (66511 / 40000) = -Real.log (40000 / 66511) := by
    rw [show ((66511 / 40000) : ℝ) = ((40000 / 66511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (217400983 / 200000000) ≤ -Real.log (13489 / 40000) ∧
    -Real.log (13489 / 40000) ≤ (1087004917 / 1000000000) := by
  have h := checkLog_sound (w := (6511 / 33489)) (n := 12)
    (lo := (78771547 / 200000000)) (hi := (49232217 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 13489) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 13489) = 1/(13489 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1087004917 / 1000000000) (-217400983 / 200000000) (Real.log (13489 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (510800623 / 1000000000) ≤ -Real.log (8000 / 13333) ∧
    -Real.log (8000 / 13333) ≤ (31925039 / 62500000) := by
  have h := checkLog_sound (w := (5333 / 21333)) (n := 12)
    (lo := (510800623 / 1000000000)) (hi := (31925039 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13333 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13333 / 8000) = 1/(8000 / 13333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (510800623 / 1000000000) (31925039 / 62500000) (Real.log (13333 / 8000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (13333 / 8000) = -Real.log (8000 / 13333) := by
    rw [show ((13333 / 8000) : ℝ) = ((8000 / 13333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (219697459 / 200000000) ≤ -Real.log (2667 / 8000) ∧
    -Real.log (2667 / 8000) ≤ (1098487297 / 1000000000) := by
  have h := checkLog_sound (w := (1333 / 6667)) (n := 12)
    (lo := (81068023 / 200000000)) (hi := (101335029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 2667) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4000 / 2667) = 1/(2667 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1098487297 / 1000000000) (-219697459 / 200000000) (Real.log (2667 / 8000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2090644061 / 1000000000) ≤ -Real.log (500000000000 / 4045062017371) ∧
    -Real.log (500000000000 / 4045062017371) ≤ (418128813 / 200000000) := by
  have h := checkLog_sound (w := (45062017371 / 8045062017371)) (n := 12)
    (lo := (11202521 / 1000000000)) (hi := (5601261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4045062017371 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4045062017371 / 4000000000000) = 1/(500000000000 / 4045062017371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2090644061 / 1000000000) (418128813 / 200000000) (Real.log (4045062017371 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4045062017371 / 500000000000) = -Real.log (500000000000 / 4045062017371) := by
    rw [show ((4045062017371 / 500000000000) : ℝ) = ((500000000000 / 4045062017371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1045610633 / 500000000) ≤ -Real.log (500000000000 / 4047397524397) ∧
    -Real.log (500000000000 / 4047397524397) ≤ (209122127 / 100000000) := by
  have h := checkLog_sound (w := (47397524397 / 8047397524397)) (n := 12)
    (lo := (5889863 / 500000000)) (hi := (11779727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4047397524397 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4047397524397 / 4000000000000) = 1/(500000000000 / 4047397524397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1045610633 / 500000000) (209122127 / 100000000) (Real.log (4047397524397 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4047397524397 / 500000000000) = -Real.log (500000000000 / 4047397524397) := by
    rw [show ((4047397524397 / 500000000000) : ℝ) = ((500000000000 / 4047397524397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1595492807 / 1000000000) ≤ -Real.log (62500000000 / 308172399733) ∧
    -Real.log (62500000000 / 308172399733) ≤ (159549281 / 100000000) := by
  have h := checkLog_sound (w := (58172399733 / 558172399733)) (n := 12)
    (lo := (209198447 / 1000000000)) (hi := (13074903 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308172399733 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(308172399733 / 250000000000) = 1/(62500000000 / 308172399733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1595492807 / 1000000000) (159549281 / 100000000) (Real.log (308172399733 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (308172399733 / 62500000000) = -Real.log (62500000000 / 308172399733) := by
    rw [show ((308172399733 / 62500000000) : ℝ) = ((62500000000 / 308172399733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (804643959 / 500000000) ≤ -Real.log (50000000000 / 249962504687) ∧
    -Real.log (50000000000 / 249962504687) ≤ (1609287921 / 1000000000) := by
  have h := checkLog_sound (w := (49962504687 / 449962504687)) (n := 12)
    (lo := (111496779 / 500000000)) (hi := (222993559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249962504687 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(249962504687 / 200000000000) = 1/(50000000000 / 249962504687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (804643959 / 500000000) (1609287921 / 1000000000) (Real.log (249962504687 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (249962504687 / 50000000000) = -Real.log (50000000000 / 249962504687) := by
    rw [show ((249962504687 / 50000000000) : ℝ) = ((50000000000 / 249962504687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0008
