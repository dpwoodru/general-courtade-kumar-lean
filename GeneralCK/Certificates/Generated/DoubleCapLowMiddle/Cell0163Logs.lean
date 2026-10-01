import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0163
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

theorem reflection_log_1_neg : (321666527 / 500000000) ≤ -Real.log (3200 / 6089) ∧
    -Real.log (3200 / 6089) ≤ (128666611 / 200000000) := by
  have h := checkLog_sound (w := (2889 / 9289)) (n := 12)
    (lo := (321666527 / 500000000)) (hi := (128666611 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6089 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6089 / 3200) = 1/(3200 / 6089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (321666527 / 500000000) (128666611 / 200000000) (Real.log (6089 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6089 / 3200) = -Real.log (3200 / 6089) := by
    rw [show ((6089 / 3200) : ℝ) = ((3200 / 6089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1165556587 / 500000000) ≤ -Real.log (311 / 3200) ∧
    -Real.log (311 / 3200) ≤ (1165556589 / 500000000) := by
  have h := checkLog_sound (w := (89 / 711)) (n := 12)
    (lo := (125835817 / 500000000)) (hi := (50334327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 311) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 311) = 1/(311 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1165556589 / 500000000) (-1165556587 / 500000000) (Real.log (311 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (128510531 / 200000000) ≤ -Real.log (12800 / 24337) ∧
    -Real.log (12800 / 24337) ≤ (40159541 / 62500000) := by
  have h := checkLog_sound (w := (11537 / 37137)) (n := 12)
    (lo := (128510531 / 200000000)) (hi := (40159541 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24337 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24337 / 12800) = 1/(12800 / 24337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (128510531 / 200000000) (40159541 / 62500000) (Real.log (24337 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24337 / 12800) = -Real.log (12800 / 24337) := by
    rw [show ((24337 / 12800) : ℝ) = ((12800 / 24337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (92638213 / 40000000) ≤ -Real.log (1263 / 12800) ∧
    -Real.log (1263 / 12800) ≤ (2315955329 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 2863)) (n := 12)
    (lo := (47302757 / 200000000)) (hi := (118256893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1263) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1263) = 1/(1263 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2315955329 / 1000000000) (-92638213 / 40000000) (Real.log (1263 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (73863349 / 125000000) ≤ -Real.log (1600 / 2889) ∧
    -Real.log (1600 / 2889) ≤ (590906793 / 1000000000) := by
  have h := checkLog_sound (w := (1289 / 4489)) (n := 12)
    (lo := (73863349 / 125000000)) (hi := (590906793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2889 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2889 / 1600) = 1/(1600 / 2889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (73863349 / 125000000) (590906793 / 1000000000) (Real.log (2889 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2889 / 1600) = -Real.log (1600 / 2889) := by
    rw [show ((2889 / 1600) : ℝ) = ((1600 / 2889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (818982997 / 500000000) ≤ -Real.log (311 / 1600) ∧
    -Real.log (311 / 1600) ≤ (1637965997 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 711)) (n := 12)
    (lo := (125835817 / 500000000)) (hi := (50334327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 311) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 311) = 1/(311 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1637965997 / 1000000000) (-818982997 / 500000000) (Real.log (311 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (589261271 / 1000000000) ≤ -Real.log (6400 / 11537) ∧
    -Real.log (6400 / 11537) ≤ (73657659 / 125000000) := by
  have h := checkLog_sound (w := (5137 / 17937)) (n := 12)
    (lo := (589261271 / 1000000000)) (hi := (73657659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11537 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11537 / 6400) = 1/(6400 / 11537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (589261271 / 1000000000) (73657659 / 125000000) (Real.log (11537 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11537 / 6400) = -Real.log (6400 / 11537) := by
    rw [show ((11537 / 6400) : ℝ) = ((6400 / 11537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (324561629 / 200000000) ≤ -Real.log (1263 / 6400) ∧
    -Real.log (1263 / 6400) ≤ (405702037 / 250000000) := by
  have h := checkLog_sound (w := (337 / 2863)) (n := 12)
    (lo := (47302757 / 200000000)) (hi := (118256893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1263) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1263) = 1/(1263 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-405702037 / 250000000) (-324561629 / 200000000) (Real.log (1263 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (65455343 / 100000000) ≤ -Real.log (1000000 / 1924283) ∧
    -Real.log (1000000 / 1924283) ≤ (654553431 / 1000000000) := by
  have h := checkLog_sound (w := (924283 / 2924283)) (n := 12)
    (lo := (65455343 / 100000000)) (hi := (654553431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1924283 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1924283 / 1000000) = 1/(1000000 / 1924283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (65455343 / 100000000) (654553431 / 1000000000) (Real.log (1924283 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1924283 / 1000000) = -Real.log (1000000 / 1924283) := by
    rw [show ((1924283 / 1000000) : ℝ) = ((1000000 / 1924283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2580752571 / 1000000000) ≤ -Real.log (75717 / 1000000) ∧
    -Real.log (75717 / 1000000) ≤ (103230103 / 40000000) := by
  have h := checkLog_sound (w := (49283 / 200717)) (n := 12)
    (lo := (501311031 / 1000000000)) (hi := (62663879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 75717) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 75717) = 1/(75717 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-103230103 / 40000000) (-2580752571 / 1000000000) (Real.log (75717 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (655081799 / 1000000000) ≤ -Real.log (10000 / 19253) ∧
    -Real.log (10000 / 19253) ≤ (3275409 / 5000000) := by
  have h := checkLog_sound (w := (9253 / 29253)) (n := 12)
    (lo := (655081799 / 1000000000)) (hi := (3275409 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19253 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19253 / 10000) = 1/(10000 / 19253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (655081799 / 1000000000) (3275409 / 5000000) (Real.log (19253 / 10000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (19253 / 10000) = -Real.log (10000 / 19253) := by
    rw [show ((19253 / 10000) : ℝ) = ((10000 / 19253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (518855037 / 200000000) ≤ -Real.log (747 / 10000) ∧
    -Real.log (747 / 10000) ≤ (2594275189 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 1997)) (n := 12)
    (lo := (102966729 / 200000000)) (hi := (257416823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 747) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1250 / 747) = 1/(747 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2594275189 / 1000000000) (-518855037 / 200000000) (Real.log (747 / 10000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (653360587 / 1000000000) ≤ -Real.log (1000000 / 1921989) ∧
    -Real.log (1000000 / 1921989) ≤ (163340147 / 250000000) := by
  have h := checkLog_sound (w := (921989 / 2921989)) (n := 12)
    (lo := (653360587 / 1000000000)) (hi := (163340147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1921989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1921989 / 1000000) = 1/(1000000 / 1921989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (653360587 / 1000000000) (163340147 / 250000000) (Real.log (1921989 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1921989 / 1000000) = -Real.log (1000000 / 1921989) := by
    rw [show ((1921989 / 1000000) : ℝ) = ((1000000 / 1921989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1275452717 / 500000000) ≤ -Real.log (78011 / 1000000) ∧
    -Real.log (78011 / 1000000) ≤ (1275452719 / 500000000) := by
  have h := checkLog_sound (w := (46989 / 203011)) (n := 12)
    (lo := (235731947 / 500000000)) (hi := (94292779 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 78011) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 78011) = 1/(78011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1275452719 / 500000000) (-1275452717 / 500000000) (Real.log (78011 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (653931187 / 1000000000) ≤ -Real.log (500000 / 961543) ∧
    -Real.log (500000 / 961543) ≤ (163482797 / 250000000) := by
  have h := checkLog_sound (w := (461543 / 1461543)) (n := 12)
    (lo := (653931187 / 1000000000)) (hi := (163482797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((961543 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(961543 / 500000) = 1/(500000 / 961543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (653931187 / 1000000000) (163482797 / 250000000) (Real.log (961543 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (961543 / 500000) = -Real.log (500000 / 961543) := by
    rw [show ((961543 / 500000) : ℝ) = ((500000 / 961543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1282533681 / 500000000) ≤ -Real.log (38457 / 500000) ∧
    -Real.log (38457 / 500000) ≤ (1282533683 / 500000000) := by
  have h := checkLog_sound (w := (24043 / 100957)) (n := 12)
    (lo := (242812911 / 500000000)) (hi := (485625823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 38457) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 38457) = 1/(38457 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1282533683 / 500000000) (-1282533681 / 500000000) (Real.log (38457 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3235306001 / 1000000000) ≤ -Real.log (250000000000 / 6353536854339) ∧
    -Real.log (250000000000 / 6353536854339) ≤ (1617653003 / 500000000) := by
  have h := checkLog_sound (w := (2353536854339 / 10353536854339)) (n := 12)
    (lo := (462717281 / 1000000000)) (hi := (231358641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6353536854339 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6353536854339 / 4000000000000) = 1/(250000000000 / 6353536854339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3235306001 / 1000000000) (1617653003 / 500000000) (Real.log (6353536854339 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6353536854339 / 250000000000) = -Real.log (250000000000 / 6353536854339) := by
    rw [show ((6353536854339 / 250000000000) : ℝ) = ((250000000000 / 6353536854339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (406169623 / 125000000) ≤ -Real.log (500000000000 / 12886880856761) ∧
    -Real.log (500000000000 / 12886880856761) ≤ (3249356989 / 1000000000) := by
  have h := checkLog_sound (w := (4886880856761 / 20886880856761)) (n := 12)
    (lo := (59596033 / 125000000)) (hi := (95353653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12886880856761 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12886880856761 / 8000000000000) = 1/(500000000000 / 12886880856761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (406169623 / 125000000) (3249356989 / 1000000000) (Real.log (12886880856761 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12886880856761 / 500000000000) = -Real.log (500000000000 / 12886880856761) := by
    rw [show ((12886880856761 / 500000000000) : ℝ) = ((500000000000 / 12886880856761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3204266021 / 1000000000) ≤ -Real.log (100000000000 / 2463741010883) ∧
    -Real.log (100000000000 / 2463741010883) ≤ (1602133013 / 500000000) := by
  have h := checkLog_sound (w := (863741010883 / 4063741010883)) (n := 12)
    (lo := (431677301 / 1000000000)) (hi := (215838651 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2463741010883 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2463741010883 / 1600000000000) = 1/(100000000000 / 2463741010883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3204266021 / 1000000000) (1602133013 / 500000000) (Real.log (2463741010883 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2463741010883 / 100000000000) = -Real.log (100000000000 / 2463741010883) := by
    rw [show ((2463741010883 / 100000000000) : ℝ) = ((100000000000 / 2463741010883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3218998549 / 1000000000) ≤ -Real.log (250000000000 / 6250767090517) ∧
    -Real.log (250000000000 / 6250767090517) ≤ (1609499277 / 500000000) := by
  have h := checkLog_sound (w := (2250767090517 / 10250767090517)) (n := 12)
    (lo := (446409829 / 1000000000)) (hi := (44640983 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250767090517 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250767090517 / 4000000000000) = 1/(250000000000 / 6250767090517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3218998549 / 1000000000) (1609499277 / 500000000) (Real.log (6250767090517 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6250767090517 / 250000000000) = -Real.log (250000000000 / 6250767090517) := by
    rw [show ((6250767090517 / 250000000000) : ℝ) = ((250000000000 / 6250767090517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0163
