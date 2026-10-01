import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell166
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (298511889 / 1000000000) ≤ -Real.log (5120 / 6901) ∧
    -Real.log (5120 / 6901) ≤ (29851189 / 100000000) := by
  have h := checkLog_sound (w := (1781 / 12021)) (n := 12)
    (lo := (298511889 / 1000000000)) (hi := (29851189 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6901 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6901 / 5120) = 1/(5120 / 6901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (298511889 / 1000000000) (29851189 / 100000000) (Real.log (6901 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6901 / 5120) = -Real.log (5120 / 6901) := by
    rw [show ((6901 / 5120) : ℝ) = ((5120 / 6901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (213741539 / 500000000) ≤ -Real.log (3339 / 5120) ∧
    -Real.log (3339 / 5120) ≤ (427483079 / 1000000000) := by
  have h := checkLog_sound (w := (1781 / 8459)) (n := 12)
    (lo := (213741539 / 500000000)) (hi := (427483079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3339) = 1/(3339 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-427483079 / 1000000000) (-213741539 / 500000000) (Real.log (3339 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11923083 / 40000000) ≤ -Real.log (2560 / 3449) ∧
    -Real.log (2560 / 3449) ≤ (74519269 / 250000000) := by
  have h := checkLog_sound (w := (889 / 6009)) (n := 12)
    (lo := (11923083 / 40000000)) (hi := (74519269 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3449 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3449 / 2560) = 1/(2560 / 3449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11923083 / 40000000) (74519269 / 250000000) (Real.log (3449 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3449 / 2560) = -Real.log (2560 / 3449) := by
    rw [show ((3449 / 2560) : ℝ) = ((2560 / 3449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (26661563 / 62500000) ≤ -Real.log (1671 / 2560) ∧
    -Real.log (1671 / 2560) ≤ (426585009 / 1000000000) := by
  have h := checkLog_sound (w := (889 / 4231)) (n := 12)
    (lo := (26661563 / 62500000)) (hi := (426585009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1671) = 1/(1671 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-426585009 / 1000000000) (-26661563 / 62500000) (Real.log (1671 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (27577847 / 125000000) ≤ -Real.log (1000000 / 1246853) ∧
    -Real.log (1000000 / 1246853) ≤ (220622777 / 1000000000) := by
  have h := checkLog_sound (w := (246853 / 2246853)) (n := 12)
    (lo := (27577847 / 125000000)) (hi := (220622777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1246853 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1246853 / 1000000) = 1/(1000000 / 1246853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (27577847 / 125000000) (220622777 / 1000000000) (Real.log (1246853 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1246853 / 1000000) = -Real.log (1000000 / 1246853) := by
    rw [show ((1246853 / 1000000) : ℝ) = ((1000000 / 1246853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (283494851 / 1000000000) ≤ -Real.log (753147 / 1000000) ∧
    -Real.log (753147 / 1000000) ≤ (70873713 / 250000000) := by
  have h := checkLog_sound (w := (246853 / 1753147)) (n := 12)
    (lo := (283494851 / 1000000000)) (hi := (70873713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 753147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 753147) = 1/(753147 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-70873713 / 250000000) (-283494851 / 1000000000) (Real.log (753147 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (220961171 / 1000000000) ≤ -Real.log (40000 / 49891) ∧
    -Real.log (40000 / 49891) ≤ (55240293 / 250000000) := by
  have h := checkLog_sound (w := (9891 / 89891)) (n := 12)
    (lo := (220961171 / 1000000000)) (hi := (55240293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49891 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49891 / 40000) = 1/(40000 / 49891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (220961171 / 1000000000) (55240293 / 250000000) (Real.log (49891 / 40000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49891 / 40000) = -Real.log (40000 / 49891) := by
    rw [show ((49891 / 40000) : ℝ) = ((40000 / 49891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (284055323 / 1000000000) ≤ -Real.log (30109 / 40000) ∧
    -Real.log (30109 / 40000) ≤ (71013831 / 250000000) := by
  have h := checkLog_sound (w := (9891 / 70109)) (n := 12)
    (lo := (284055323 / 1000000000)) (hi := (71013831 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 30109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 30109) = 1/(30109 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-71013831 / 250000000) (-284055323 / 1000000000) (Real.log (30109 / 40000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (163435159 / 1000000000) ≤ -Real.log (1000000 / 1177549) ∧
    -Real.log (1000000 / 1177549) ≤ (4085879 / 25000000) := by
  have h := checkLog_sound (w := (177549 / 2177549)) (n := 12)
    (lo := (163435159 / 1000000000)) (hi := (4085879 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177549 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1177549 / 1000000) = 1/(1000000 / 1177549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (163435159 / 1000000000) (4085879 / 25000000) (Real.log (1177549 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1177549 / 1000000) = -Real.log (1000000 / 1177549) := by
    rw [show ((1177549 / 1000000) : ℝ) = ((1000000 / 1177549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (48866593 / 250000000) ≤ -Real.log (822451 / 1000000) ∧
    -Real.log (822451 / 1000000) ≤ (195466373 / 1000000000) := by
  have h := checkLog_sound (w := (177549 / 1822451)) (n := 12)
    (lo := (48866593 / 250000000)) (hi := (195466373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 822451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 822451) = 1/(822451 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-195466373 / 1000000000) (-48866593 / 250000000) (Real.log (822451 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (163701779 / 1000000000) ≤ -Real.log (1000000 / 1177863) ∧
    -Real.log (1000000 / 1177863) ≤ (8185089 / 50000000) := by
  have h := checkLog_sound (w := (177863 / 2177863)) (n := 12)
    (lo := (163701779 / 1000000000)) (hi := (8185089 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1177863 / 1000000) = 1/(1000000 / 1177863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (163701779 / 1000000000) (8185089 / 50000000) (Real.log (1177863 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1177863 / 1000000) = -Real.log (1000000 / 1177863) := by
    rw [show ((1177863 / 1000000) : ℝ) = ((1000000 / 1177863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (195848231 / 1000000000) ≤ -Real.log (822137 / 1000000) ∧
    -Real.log (822137 / 1000000) ≤ (24481029 / 125000000) := by
  have h := checkLog_sound (w := (177863 / 1822137)) (n := 12)
    (lo := (195848231 / 1000000000)) (hi := (24481029 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 822137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 822137) = 1/(822137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-24481029 / 125000000) (-195848231 / 1000000000) (Real.log (822137 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (724662083 / 1000000000) ≤ -Real.log (500000000000 / 1032016756433) ∧
    -Real.log (500000000000 / 1032016756433) ≤ (144932417 / 200000000) := by
  have h := checkLog_sound (w := (32016756433 / 2032016756433)) (n := 12)
    (lo := (31514903 / 1000000000)) (hi := (3939363 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1032016756433 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1032016756433 / 1000000000000) = 1/(500000000000 / 1032016756433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (724662083 / 1000000000) (144932417 / 200000000) (Real.log (1032016756433 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1032016756433 / 500000000000) = -Real.log (500000000000 / 1032016756433) := by
    rw [show ((1032016756433 / 500000000000) : ℝ) = ((500000000000 / 1032016756433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (725994967 / 1000000000) ≤ -Real.log (500000000000 / 1033393231507) ∧
    -Real.log (500000000000 / 1033393231507) ≤ (725994969 / 1000000000) := by
  have h := checkLog_sound (w := (33393231507 / 2033393231507)) (n := 12)
    (lo := (32847787 / 1000000000)) (hi := (8211947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1033393231507 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1033393231507 / 1000000000000) = 1/(500000000000 / 1033393231507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (725994967 / 1000000000) (725994969 / 1000000000) (Real.log (1033393231507 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1033393231507 / 500000000000) = -Real.log (500000000000 / 1033393231507) := by
    rw [show ((1033393231507 / 500000000000) : ℝ) = ((500000000000 / 1033393231507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (504117627 / 1000000000) ≤ -Real.log (500000000000 / 827762043797) ∧
    -Real.log (500000000000 / 827762043797) ≤ (126029407 / 250000000) := by
  have h := checkLog_sound (w := (327762043797 / 1327762043797)) (n := 12)
    (lo := (504117627 / 1000000000)) (hi := (126029407 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827762043797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827762043797 / 500000000000) = 1/(500000000000 / 827762043797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (504117627 / 1000000000) (126029407 / 250000000) (Real.log (827762043797 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (827762043797 / 500000000000) = -Real.log (500000000000 / 827762043797) := by
    rw [show ((827762043797 / 500000000000) : ℝ) = ((500000000000 / 827762043797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (101003299 / 200000000) ≤ -Real.log (10000000000 / 16570128533) ∧
    -Real.log (10000000000 / 16570128533) ≤ (31563531 / 62500000) := by
  have h := checkLog_sound (w := (6570128533 / 26570128533)) (n := 12)
    (lo := (101003299 / 200000000)) (hi := (31563531 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16570128533 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16570128533 / 10000000000) = 1/(10000000000 / 16570128533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (101003299 / 200000000) (31563531 / 62500000) (Real.log (16570128533 / 10000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (16570128533 / 10000000000) = -Real.log (10000000000 / 16570128533) := by
    rw [show ((16570128533 / 10000000000) : ℝ) = ((10000000000 / 16570128533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (89725383 / 250000000) ≤ -Real.log (125000000000 / 178969476601) ∧
    -Real.log (125000000000 / 178969476601) ≤ (358901533 / 1000000000) := by
  have h := checkLog_sound (w := (53969476601 / 303969476601)) (n := 12)
    (lo := (89725383 / 250000000)) (hi := (358901533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178969476601 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178969476601 / 125000000000) = 1/(125000000000 / 178969476601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (89725383 / 250000000) (358901533 / 1000000000) (Real.log (178969476601 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (178969476601 / 125000000000) = -Real.log (125000000000 / 178969476601) := by
    rw [show ((178969476601 / 125000000000) : ℝ) = ((125000000000 / 178969476601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (35955001 / 100000000) ≤ -Real.log (500000000000 / 716342288451) ∧
    -Real.log (500000000000 / 716342288451) ≤ (359550011 / 1000000000) := by
  have h := checkLog_sound (w := (216342288451 / 1216342288451)) (n := 12)
    (lo := (35955001 / 100000000)) (hi := (359550011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716342288451 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716342288451 / 500000000000) = 1/(500000000000 / 716342288451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (35955001 / 100000000) (359550011 / 1000000000) (Real.log (716342288451 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (716342288451 / 500000000000) = -Real.log (500000000000 / 716342288451) := by
    rw [show ((716342288451 / 500000000000) : ℝ) = ((500000000000 / 716342288451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (32146451 / 1000000000) ≤ -Real.log (968364753231 / 1000000000000) ∧
    -Real.log (968364753231 / 1000000000000) ≤ (8036613 / 250000000) := by
  have h := checkLog_sound (w := (31635246769 / 1968364753231)) (n := 12)
    (lo := (32146451 / 1000000000)) (hi := (8036613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968364753231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968364753231) = 1/(968364753231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8036613 / 250000000) (-32146451 / 1000000000) (Real.log (968364753231 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8007803 / 250000000) ≤ -Real.log (968476352599 / 1000000000000) ∧
    -Real.log (968476352599 / 1000000000000) ≤ (32031213 / 1000000000) := by
  have h := checkLog_sound (w := (31523647401 / 1968476352599)) (n := 12)
    (lo := (8007803 / 250000000)) (hi := (32031213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968476352599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968476352599) = 1/(968476352599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-32031213 / 1000000000) (-8007803 / 250000000) (Real.log (968476352599 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell166
