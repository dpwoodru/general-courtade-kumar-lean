import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0123
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

theorem reflection_log_1_neg : (156948957 / 500000000) ≤ -Real.log (160 / 219) ∧
    -Real.log (160 / 219) ≤ (62779583 / 200000000) := by
  have h := checkLog_sound (w := (59 / 379)) (n := 12)
    (lo := (156948957 / 500000000)) (hi := (62779583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219 / 160) = 1/(160 / 219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (156948957 / 500000000) (62779583 / 200000000) (Real.log (219 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (219 / 160) = -Real.log (160 / 219) := by
    rw [show ((219 / 160) : ℝ) = ((160 / 219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (230026649 / 500000000) ≤ -Real.log (101 / 160) ∧
    -Real.log (101 / 160) ≤ (460053299 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 261)) (n := 12)
    (lo := (230026649 / 500000000)) (hi := (460053299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 101) = 1/(101 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-460053299 / 1000000000) (-230026649 / 500000000) (Real.log (101 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (313041383 / 1000000000) ≤ -Real.log (2560 / 3501) ∧
    -Real.log (2560 / 3501) ≤ (39130173 / 125000000) := by
  have h := checkLog_sound (w := (941 / 6061)) (n := 12)
    (lo := (313041383 / 1000000000)) (hi := (39130173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3501 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3501 / 2560) = 1/(2560 / 3501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (313041383 / 1000000000) (39130173 / 125000000) (Real.log (3501 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3501 / 2560) = -Real.log (2560 / 3501) := by
    rw [show ((3501 / 2560) : ℝ) = ((2560 / 3501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (458198583 / 1000000000) ≤ -Real.log (1619 / 2560) ∧
    -Real.log (1619 / 2560) ≤ (57274823 / 125000000) := by
  have h := checkLog_sound (w := (941 / 4179)) (n := 12)
    (lo := (458198583 / 1000000000)) (hi := (57274823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1619) = 1/(1619 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-57274823 / 125000000) (-458198583 / 1000000000) (Real.log (1619 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (276223649 / 500000000) ≤ -Real.log (80 / 139) ∧
    -Real.log (80 / 139) ≤ (552447299 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 219)) (n := 12)
    (lo := (276223649 / 500000000)) (hi := (552447299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139 / 80) = 1/(80 / 139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (276223649 / 500000000) (552447299 / 1000000000) (Real.log (139 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (139 / 80) = -Real.log (80 / 139) := by
    rw [show ((139 / 80) : ℝ) = ((80 / 139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (334376049 / 250000000) ≤ -Real.log (21 / 80) ∧
    -Real.log (21 / 80) ≤ (668752099 / 500000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 21) = 1/(21 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-668752099 / 500000000) (-334376049 / 250000000) (Real.log (21 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (275548733 / 500000000) ≤ -Real.log (1280 / 2221) ∧
    -Real.log (1280 / 2221) ≤ (551097467 / 1000000000) := by
  have h := checkLog_sound (w := (941 / 3501)) (n := 12)
    (lo := (275548733 / 500000000)) (hi := (551097467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2221 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2221 / 1280) = 1/(1280 / 2221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (275548733 / 500000000) (551097467 / 1000000000) (Real.log (2221 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2221 / 1280) = -Real.log (1280 / 2221) := by
    rw [show ((2221 / 1280) : ℝ) = ((1280 / 2221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (83038453 / 62500000) ≤ -Real.log (339 / 1280) ∧
    -Real.log (339 / 1280) ≤ (5314461 / 4000000) := by
  have h := checkLog_sound (w := (301 / 979)) (n := 12)
    (lo := (158867017 / 250000000)) (hi := (635468069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 339) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 339) = 1/(339 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-5314461 / 4000000) (-83038453 / 62500000) (Real.log (339 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (428773999 / 1000000000) ≤ -Real.log (500000 / 767687) ∧
    -Real.log (500000 / 767687) ≤ (214387 / 500000) := by
  have h := checkLog_sound (w := (267687 / 1267687)) (n := 12)
    (lo := (428773999 / 1000000000)) (hi := (214387 / 500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((767687 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(767687 / 500000) = 1/(500000 / 767687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (428773999 / 1000000000) (214387 / 500000) (Real.log (767687 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (767687 / 500000) = -Real.log (500000 / 767687) := by
    rw [show ((767687 / 500000) : ℝ) = ((500000 / 767687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (766522497 / 1000000000) ≤ -Real.log (232313 / 500000) ∧
    -Real.log (232313 / 500000) ≤ (766522499 / 1000000000) := by
  have h := checkLog_sound (w := (17687 / 482313)) (n := 12)
    (lo := (73375317 / 1000000000)) (hi := (36687659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 232313) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 232313) = 1/(232313 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-766522499 / 1000000000) (-766522497 / 1000000000) (Real.log (232313 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (429974939 / 1000000000) ≤ -Real.log (1000000 / 1537219) ∧
    -Real.log (1000000 / 1537219) ≤ (21498747 / 50000000) := by
  have h := checkLog_sound (w := (537219 / 2537219)) (n := 12)
    (lo := (429974939 / 1000000000)) (hi := (21498747 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1537219 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1537219 / 1000000) = 1/(1000000 / 1537219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (429974939 / 1000000000) (21498747 / 50000000) (Real.log (1537219 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1537219 / 1000000) = -Real.log (1000000 / 1537219) := by
    rw [show ((1537219 / 1000000) : ℝ) = ((1000000 / 1537219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (385250669 / 500000000) ≤ -Real.log (462781 / 1000000) ∧
    -Real.log (462781 / 1000000) ≤ (38525067 / 50000000) := by
  have h := checkLog_sound (w := (37219 / 962781)) (n := 12)
    (lo := (38677079 / 500000000)) (hi := (77354159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 462781) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 462781) = 1/(462781 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-38525067 / 50000000) (-385250669 / 500000000) (Real.log (462781 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (43039283 / 125000000) ≤ -Real.log (500000 / 705511) ∧
    -Real.log (500000 / 705511) ≤ (68862853 / 200000000) := by
  have h := checkLog_sound (w := (205511 / 1205511)) (n := 12)
    (lo := (43039283 / 125000000)) (hi := (68862853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705511 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705511 / 500000) = 1/(500000 / 705511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (43039283 / 125000000) (68862853 / 200000000) (Real.log (705511 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (705511 / 500000) = -Real.log (500000 / 705511) := by
    rw [show ((705511 / 500000) : ℝ) = ((500000 / 705511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (529366447 / 1000000000) ≤ -Real.log (294489 / 500000) ∧
    -Real.log (294489 / 500000) ≤ (33085403 / 62500000) := by
  have h := checkLog_sound (w := (205511 / 794489)) (n := 12)
    (lo := (529366447 / 1000000000)) (hi := (33085403 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 294489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 294489) = 1/(294489 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-33085403 / 62500000) (-529366447 / 1000000000) (Real.log (294489 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (345489317 / 1000000000) ≤ -Real.log (1000000 / 1412681) ∧
    -Real.log (1000000 / 1412681) ≤ (172744659 / 500000000) := by
  have h := checkLog_sound (w := (412681 / 2412681)) (n := 12)
    (lo := (345489317 / 1000000000)) (hi := (172744659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1412681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1412681 / 1000000) = 1/(1000000 / 1412681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (345489317 / 1000000000) (172744659 / 500000000) (Real.log (1412681 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1412681 / 1000000) = -Real.log (1000000 / 1412681) := by
    rw [show ((1412681 / 1000000) : ℝ) = ((1000000 / 1412681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (106437433 / 200000000) ≤ -Real.log (587319 / 1000000) ∧
    -Real.log (587319 / 1000000) ≤ (266093583 / 500000000) := by
  have h := checkLog_sound (w := (412681 / 1587319)) (n := 12)
    (lo := (106437433 / 200000000)) (hi := (266093583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 587319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 587319) = 1/(587319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-266093583 / 500000000) (-106437433 / 200000000) (Real.log (587319 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1195296497 / 1000000000) ≤ -Real.log (500000000000 / 1652268706443) ∧
    -Real.log (500000000000 / 1652268706443) ≤ (1195296499 / 1000000000) := by
  have h := checkLog_sound (w := (652268706443 / 2652268706443)) (n := 12)
    (lo := (502149317 / 1000000000)) (hi := (251074659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1652268706443 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1652268706443 / 1000000000000) = 1/(500000000000 / 1652268706443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1195296497 / 1000000000) (1195296499 / 1000000000) (Real.log (1652268706443 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1652268706443 / 500000000000) = -Real.log (500000000000 / 1652268706443) := by
    rw [show ((1652268706443 / 500000000000) : ℝ) = ((500000000000 / 1652268706443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (600238139 / 500000000) ≤ -Real.log (500000000000 / 1660849300209) ∧
    -Real.log (500000000000 / 1660849300209) ≤ (30011907 / 25000000) := by
  have h := checkLog_sound (w := (660849300209 / 2660849300209)) (n := 12)
    (lo := (253664549 / 500000000)) (hi := (507329099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1660849300209 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1660849300209 / 1000000000000) = 1/(500000000000 / 1660849300209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (600238139 / 500000000) (30011907 / 25000000) (Real.log (1660849300209 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1660849300209 / 500000000000) = -Real.log (500000000000 / 1660849300209) := by
    rw [show ((1660849300209 / 500000000000) : ℝ) = ((500000000000 / 1660849300209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (873680711 / 1000000000) ≤ -Real.log (125000000000 / 299464071663) ∧
    -Real.log (125000000000 / 299464071663) ≤ (873680713 / 1000000000) := by
  have h := checkLog_sound (w := (49464071663 / 549464071663)) (n := 12)
    (lo := (180533531 / 1000000000)) (hi := (45133383 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299464071663 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(299464071663 / 250000000000) = 1/(125000000000 / 299464071663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (873680711 / 1000000000) (873680713 / 1000000000) (Real.log (299464071663 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (299464071663 / 125000000000) = -Real.log (125000000000 / 299464071663) := by
    rw [show ((299464071663 / 125000000000) : ℝ) = ((125000000000 / 299464071663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (438838241 / 500000000) ≤ -Real.log (250000000000 / 601326110683) ∧
    -Real.log (250000000000 / 601326110683) ≤ (219419121 / 250000000) := by
  have h := checkLog_sound (w := (101326110683 / 1101326110683)) (n := 12)
    (lo := (92264651 / 500000000)) (hi := (184529303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601326110683 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(601326110683 / 500000000000) = 1/(250000000000 / 601326110683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (438838241 / 500000000) (219419121 / 250000000) (Real.log (601326110683 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (601326110683 / 250000000000) = -Real.log (250000000000 / 601326110683) := by
    rw [show ((601326110683 / 250000000000) : ℝ) = ((250000000000 / 601326110683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0123
