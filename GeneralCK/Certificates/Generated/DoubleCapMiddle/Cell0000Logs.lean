import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0000
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

theorem reflection_log_1_neg : (470003629 / 1000000000) ≤ -Real.log (5 / 8) ∧
    -Real.log (5 / 8) ≤ (47000363 / 100000000) := by
  have h := checkLog_sound (w := (3 / 13)) (n := 12)
    (lo := (470003629 / 1000000000)) (hi := (47000363 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8 / 5) = 1/(5 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (470003629 / 1000000000) (47000363 / 100000000) (Real.log (8 / 5)) := by
  have h := reflection_log_1_neg
  have he : Real.log (8 / 5) = -Real.log (5 / 8) := by
    rw [show ((8 / 5) : ℝ) = ((5 / 8) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (916290731 / 1000000000) ≤ -Real.log (2 / 5) ∧
    -Real.log (2 / 5) ≤ (916290733 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5 / 4) = 1/(2 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-916290733 / 1000000000) (-916290731 / 1000000000) (Real.log (2 / 5)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (462160451 / 1000000000) ≤ -Real.log (80 / 127) ∧
    -Real.log (80 / 127) ≤ (115540113 / 250000000) := by
  have h := checkLog_sound (w := (47 / 207)) (n := 12)
    (lo := (462160451 / 1000000000)) (hi := (115540113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127 / 80) = 1/(80 / 127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (462160451 / 1000000000) (115540113 / 250000000) (Real.log (127 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (127 / 80) = -Real.log (80 / 127) := by
    rw [show ((127 / 80) : ℝ) = ((80 / 127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (27672471 / 31250000) ≤ -Real.log (33 / 80) ∧
    -Real.log (33 / 80) ≤ (442759537 / 500000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 33) = 1/(33 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-442759537 / 500000000) (-27672471 / 31250000) (Real.log (33 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45580389 / 250000000) ≤ -Real.log (5 / 6) ∧
    -Real.log (5 / 6) ≤ (182321557 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 11)) (n := 12)
    (lo := (45580389 / 250000000)) (hi := (182321557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6 / 5) = 1/(5 / 6) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45580389 / 250000000) (182321557 / 1000000000) (Real.log (6 / 5)) := by
  have h := reflection_log_5_neg
  have he : Real.log (6 / 5) = -Real.log (5 / 6) := by
    rw [show ((6 / 5) : ℝ) = ((5 / 6) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (223143551 / 1000000000) ≤ -Real.log (4 / 5) ∧
    -Real.log (4 / 5) ≤ (1743309 / 7812500) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 4) = 1/(4 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1743309 / 7812500) (-223143551 / 1000000000) (Real.log (4 / 5)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (161268147 / 1000000000) ≤ -Real.log (40 / 47) ∧
    -Real.log (40 / 47) ≤ (40317037 / 250000000) := by
  have h := checkLog_sound (w := (7 / 87)) (n := 12)
    (lo := (161268147 / 1000000000)) (hi := (40317037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47 / 40) = 1/(40 / 47) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (161268147 / 1000000000) (40317037 / 250000000) (Real.log (47 / 40)) := by
  have h := reflection_log_7_neg
  have he : Real.log (47 / 40) = -Real.log (40 / 47) := by
    rw [show ((47 / 40) : ℝ) = ((40 / 47) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (48092973 / 250000000) ≤ -Real.log (33 / 40) ∧
    -Real.log (33 / 40) ≤ (192371893 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 33) = 1/(33 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-192371893 / 1000000000) (-48092973 / 250000000) (Real.log (33 / 40)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (580673089 / 1000000000) ≤ -Real.log (1000000 / 1787241) ∧
    -Real.log (1000000 / 1787241) ≤ (58067309 / 100000000) := by
  have h := checkLog_sound (w := (787241 / 2787241)) (n := 12)
    (lo := (580673089 / 1000000000)) (hi := (58067309 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1787241 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1787241 / 1000000) = 1/(1000000 / 1787241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (580673089 / 1000000000) (58067309 / 100000000) (Real.log (1787241 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1787241 / 1000000) = -Real.log (1000000 / 1787241) := by
    rw [show ((1787241 / 1000000) : ℝ) = ((1000000 / 1787241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (193449401 / 125000000) ≤ -Real.log (212759 / 1000000) ∧
    -Real.log (212759 / 1000000) ≤ (1547595211 / 1000000000) := by
  have h := checkLog_sound (w := (37241 / 462759)) (n := 12)
    (lo := (10081303 / 62500000)) (hi := (161300849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212759) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 212759) = 1/(212759 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1547595211 / 1000000000) (-193449401 / 125000000) (Real.log (212759 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (145479173 / 250000000) ≤ -Real.log (200000 / 357893) ∧
    -Real.log (200000 / 357893) ≤ (581916693 / 1000000000) := by
  have h := checkLog_sound (w := (157893 / 557893)) (n := 12)
    (lo := (145479173 / 250000000)) (hi := (581916693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357893 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357893 / 200000) = 1/(200000 / 357893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (145479173 / 250000000) (581916693 / 1000000000) (Real.log (357893 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (357893 / 200000) = -Real.log (200000 / 357893) := by
    rw [show ((357893 / 200000) : ℝ) = ((200000 / 357893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1558103367 / 1000000000) ≤ -Real.log (42107 / 200000) ∧
    -Real.log (42107 / 200000) ≤ (155810337 / 100000000) := by
  have h := checkLog_sound (w := (7893 / 92107)) (n := 12)
    (lo := (171809007 / 1000000000)) (hi := (10738063 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42107) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 42107) = 1/(42107 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-155810337 / 100000000) (-1558103367 / 1000000000) (Real.log (42107 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (107649127 / 200000000) ≤ -Real.log (1000000 / 1712999) ∧
    -Real.log (1000000 / 1712999) ≤ (134561409 / 250000000) := by
  have h := checkLog_sound (w := (712999 / 2712999)) (n := 12)
    (lo := (107649127 / 200000000)) (hi := (134561409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1712999 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1712999 / 1000000) = 1/(1000000 / 1712999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (107649127 / 200000000) (134561409 / 250000000) (Real.log (1712999 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1712999 / 1000000) = -Real.log (1000000 / 1712999) := by
    rw [show ((1712999 / 1000000) : ℝ) = ((1000000 / 1712999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (624134789 / 500000000) ≤ -Real.log (287001 / 1000000) ∧
    -Real.log (287001 / 1000000) ≤ (62413479 / 50000000) := by
  have h := checkLog_sound (w := (212999 / 787001)) (n := 12)
    (lo := (277561199 / 500000000)) (hi := (555122399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 287001) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 287001) = 1/(287001 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-62413479 / 50000000) (-624134789 / 500000000) (Real.log (287001 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (21711293 / 40000000) ≤ -Real.log (250000 / 430197) ∧
    -Real.log (250000 / 430197) ≤ (271391163 / 500000000) := by
  have h := checkLog_sound (w := (180197 / 680197)) (n := 12)
    (lo := (21711293 / 40000000)) (hi := (271391163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((430197 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(430197 / 250000) = 1/(250000 / 430197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21711293 / 40000000) (271391163 / 500000000) (Real.log (430197 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (430197 / 250000) = -Real.log (250000 / 430197) := by
    rw [show ((430197 / 250000) : ℝ) = ((250000 / 430197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (159472991 / 125000000) ≤ -Real.log (69803 / 250000) ∧
    -Real.log (69803 / 250000) ≤ (127578393 / 100000000) := by
  have h := checkLog_sound (w := (55197 / 194803)) (n := 12)
    (lo := (145659187 / 250000000)) (hi := (582636749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 69803) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 69803) = 1/(69803 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-127578393 / 100000000) (-159472991 / 125000000) (Real.log (69803 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2128268297 / 1000000000) ≤ -Real.log (20000000000 / 168006147801) ∧
    -Real.log (20000000000 / 168006147801) ≤ (2128268301 / 1000000000) := by
  have h := checkLog_sound (w := (8006147801 / 328006147801)) (n := 12)
    (lo := (48826757 / 1000000000)) (hi := (24413379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168006147801 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(168006147801 / 160000000000) = 1/(20000000000 / 168006147801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2128268297 / 1000000000) (2128268301 / 1000000000) (Real.log (168006147801 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (168006147801 / 20000000000) = -Real.log (20000000000 / 168006147801) := by
    rw [show ((168006147801 / 20000000000) : ℝ) = ((20000000000 / 168006147801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2140020059 / 1000000000) ≤ -Real.log (500000000000 / 4249804070583) ∧
    -Real.log (500000000000 / 4249804070583) ≤ (2140020063 / 1000000000) := by
  have h := checkLog_sound (w := (249804070583 / 8249804070583)) (n := 12)
    (lo := (60578519 / 1000000000)) (hi := (1514463 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4249804070583 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4249804070583 / 4000000000000) = 1/(500000000000 / 4249804070583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2140020059 / 1000000000) (2140020063 / 1000000000) (Real.log (4249804070583 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4249804070583 / 500000000000) = -Real.log (500000000000 / 4249804070583) := by
    rw [show ((4249804070583 / 500000000000) : ℝ) = ((500000000000 / 4249804070583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1786515213 / 1000000000) ≤ -Real.log (500000000000 / 2984308417043) ∧
    -Real.log (500000000000 / 2984308417043) ≤ (111657201 / 62500000) := by
  have h := checkLog_sound (w := (984308417043 / 4984308417043)) (n := 12)
    (lo := (400220853 / 1000000000)) (hi := (200110427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2984308417043 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2984308417043 / 2000000000000) = 1/(500000000000 / 2984308417043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1786515213 / 1000000000) (111657201 / 62500000) (Real.log (2984308417043 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2984308417043 / 500000000000) = -Real.log (500000000000 / 2984308417043) := by
    rw [show ((2984308417043 / 500000000000) : ℝ) = ((500000000000 / 2984308417043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1818566253 / 1000000000) ≤ -Real.log (500000000000 / 3081507958111) ∧
    -Real.log (500000000000 / 3081507958111) ≤ (113660391 / 62500000) := by
  have h := checkLog_sound (w := (1081507958111 / 5081507958111)) (n := 12)
    (lo := (432271893 / 1000000000)) (hi := (216135947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3081507958111 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3081507958111 / 2000000000000) = 1/(500000000000 / 3081507958111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1818566253 / 1000000000) (113660391 / 62500000) (Real.log (3081507958111 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3081507958111 / 500000000000) = -Real.log (500000000000 / 3081507958111) := by
    rw [show ((3081507958111 / 500000000000) : ℝ) = ((500000000000 / 3081507958111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0000
