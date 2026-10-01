import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell117
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

theorem reflection_log_1_neg : (138490241 / 500000000) ≤ -Real.log (2560 / 3377) ∧
    -Real.log (2560 / 3377) ≤ (276980483 / 1000000000) := by
  have h := checkLog_sound (w := (817 / 5937)) (n := 12)
    (lo := (138490241 / 500000000)) (hi := (276980483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3377 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3377 / 2560) = 1/(2560 / 3377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (138490241 / 500000000) (276980483 / 1000000000) (Real.log (3377 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3377 / 2560) = -Real.log (2560 / 3377) := by
    rw [show ((3377 / 2560) : ℝ) = ((2560 / 3377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (384399491 / 1000000000) ≤ -Real.log (1743 / 2560) ∧
    -Real.log (1743 / 2560) ≤ (96099873 / 250000000) := by
  have h := checkLog_sound (w := (817 / 4303)) (n := 12)
    (lo := (384399491 / 1000000000)) (hi := (96099873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1743) = 1/(1743 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-96099873 / 250000000) (-384399491 / 1000000000) (Real.log (1743 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (276536203 / 1000000000) ≤ -Real.log (5120 / 6751) ∧
    -Real.log (5120 / 6751) ≤ (69134051 / 250000000) := by
  have h := checkLog_sound (w := (1631 / 11871)) (n := 12)
    (lo := (276536203 / 1000000000)) (hi := (69134051 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6751 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6751 / 5120) = 1/(5120 / 6751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (276536203 / 1000000000) (69134051 / 250000000) (Real.log (6751 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6751 / 5120) = -Real.log (5120 / 6751) := by
    rw [show ((6751 / 5120) : ℝ) = ((5120 / 6751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (95884819 / 250000000) ≤ -Real.log (3489 / 5120) ∧
    -Real.log (3489 / 5120) ≤ (383539277 / 1000000000) := by
  have h := checkLog_sound (w := (1631 / 8609)) (n := 12)
    (lo := (95884819 / 250000000)) (hi := (383539277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3489) = 1/(3489 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-383539277 / 1000000000) (-95884819 / 250000000) (Real.log (3489 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (203957469 / 1000000000) ≤ -Real.log (500000 / 613123) ∧
    -Real.log (500000 / 613123) ≤ (20395747 / 100000000) := by
  have h := checkLog_sound (w := (113123 / 1113123)) (n := 12)
    (lo := (203957469 / 1000000000)) (hi := (20395747 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613123 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613123 / 500000) = 1/(500000 / 613123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (203957469 / 1000000000) (20395747 / 100000000) (Real.log (613123 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (613123 / 500000) = -Real.log (500000 / 613123) := by
    rw [show ((613123 / 500000) : ℝ) = ((500000 / 613123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (51300257 / 200000000) ≤ -Real.log (386877 / 500000) ∧
    -Real.log (386877 / 500000) ≤ (128250643 / 500000000) := by
  have h := checkLog_sound (w := (113123 / 886877)) (n := 12)
    (lo := (51300257 / 200000000)) (hi := (128250643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386877) = 1/(386877 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-128250643 / 500000000) (-51300257 / 200000000) (Real.log (386877 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (40860147 / 200000000) ≤ -Real.log (1000000 / 1226667) ∧
    -Real.log (1000000 / 1226667) ≤ (3192199 / 15625000) := by
  have h := checkLog_sound (w := (226667 / 2226667)) (n := 12)
    (lo := (40860147 / 200000000)) (hi := (3192199 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1226667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1226667 / 1000000) = 1/(1000000 / 1226667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (40860147 / 200000000) (3192199 / 15625000) (Real.log (1226667 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1226667 / 1000000) = -Real.log (1000000 / 1226667) := by
    rw [show ((1226667 / 1000000) : ℝ) = ((1000000 / 1226667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (128522767 / 500000000) ≤ -Real.log (773333 / 1000000) ∧
    -Real.log (773333 / 1000000) ≤ (51409107 / 200000000) := by
  have h := checkLog_sound (w := (226667 / 1773333)) (n := 12)
    (lo := (128522767 / 500000000)) (hi := (51409107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 773333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 773333) = 1/(773333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-51409107 / 200000000) (-128522767 / 500000000) (Real.log (773333 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (75192657 / 500000000) ≤ -Real.log (500000 / 581141) ∧
    -Real.log (500000 / 581141) ≤ (30077063 / 200000000) := by
  have h := checkLog_sound (w := (81141 / 1081141)) (n := 12)
    (lo := (75192657 / 500000000)) (hi := (30077063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581141 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581141 / 500000) = 1/(500000 / 581141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (75192657 / 500000000) (30077063 / 200000000) (Real.log (581141 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (581141 / 500000) = -Real.log (500000 / 581141) := by
    rw [show ((581141 / 500000) : ℝ) = ((500000 / 581141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (141659 / 800000) ≤ -Real.log (418859 / 500000) ∧
    -Real.log (418859 / 500000) ≤ (177073751 / 1000000000) := by
  have h := checkLog_sound (w := (81141 / 918859)) (n := 12)
    (lo := (141659 / 800000)) (hi := (177073751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 418859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 418859) = 1/(418859 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-177073751 / 1000000000) (-141659 / 800000) (Real.log (418859 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (30130571 / 200000000) ≤ -Real.log (1000000 / 1162593) ∧
    -Real.log (1000000 / 1162593) ≤ (18831607 / 125000000) := by
  have h := checkLog_sound (w := (162593 / 2162593)) (n := 12)
    (lo := (30130571 / 200000000)) (hi := (18831607 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1162593 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1162593 / 1000000) = 1/(1000000 / 1162593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (30130571 / 200000000) (18831607 / 125000000) (Real.log (1162593 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1162593 / 1000000) = -Real.log (1000000 / 1162593) := by
    rw [show ((1162593 / 1000000) : ℝ) = ((1000000 / 1162593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (88722533 / 500000000) ≤ -Real.log (837407 / 1000000) ∧
    -Real.log (837407 / 1000000) ≤ (177445067 / 1000000000) := by
  have h := checkLog_sound (w := (162593 / 1837407)) (n := 12)
    (lo := (88722533 / 500000000)) (hi := (177445067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 837407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 837407) = 1/(837407 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-177445067 / 1000000000) (-88722533 / 500000000) (Real.log (837407 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (660075479 / 1000000000) ≤ -Real.log (500000000000 / 967469188879) ∧
    -Real.log (500000000000 / 967469188879) ≤ (16501887 / 25000000) := by
  have h := checkLog_sound (w := (467469188879 / 1467469188879)) (n := 12)
    (lo := (660075479 / 1000000000)) (hi := (16501887 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((967469188879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(967469188879 / 500000000000) = 1/(500000000000 / 967469188879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (660075479 / 1000000000) (16501887 / 25000000) (Real.log (967469188879 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (967469188879 / 500000000000) = -Real.log (500000000000 / 967469188879) := by
    rw [show ((967469188879 / 500000000000) : ℝ) = ((500000000000 / 967469188879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (330689987 / 500000000) ≤ -Real.log (250000000000 / 484366035571) ∧
    -Real.log (250000000000 / 484366035571) ≤ (26455199 / 40000000) := by
  have h := checkLog_sound (w := (234366035571 / 734366035571)) (n := 12)
    (lo := (330689987 / 500000000)) (hi := (26455199 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484366035571 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(484366035571 / 250000000000) = 1/(250000000000 / 484366035571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (330689987 / 500000000) (26455199 / 40000000) (Real.log (484366035571 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (484366035571 / 250000000000) = -Real.log (250000000000 / 484366035571) := by
    rw [show ((484366035571 / 250000000000) : ℝ) = ((250000000000 / 484366035571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (92091751 / 200000000) ≤ -Real.log (500000000000 / 792400427009) ∧
    -Real.log (500000000000 / 792400427009) ≤ (115114689 / 250000000) := by
  have h := checkLog_sound (w := (292400427009 / 1292400427009)) (n := 12)
    (lo := (92091751 / 200000000)) (hi := (115114689 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792400427009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792400427009 / 500000000000) = 1/(500000000000 / 792400427009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (92091751 / 200000000) (115114689 / 250000000) (Real.log (792400427009 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (792400427009 / 500000000000) = -Real.log (500000000000 / 792400427009) := by
    rw [show ((792400427009 / 500000000000) : ℝ) = ((500000000000 / 792400427009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (461346269 / 1000000000) ≤ -Real.log (500000000000 / 793104005649) ∧
    -Real.log (500000000000 / 793104005649) ≤ (46134627 / 100000000) := by
  have h := checkLog_sound (w := (293104005649 / 1293104005649)) (n := 12)
    (lo := (461346269 / 1000000000)) (hi := (46134627 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793104005649 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(793104005649 / 500000000000) = 1/(500000000000 / 793104005649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (461346269 / 1000000000) (46134627 / 100000000) (Real.log (793104005649 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (793104005649 / 500000000000) = -Real.log (500000000000 / 793104005649) := by
    rw [show ((793104005649 / 500000000000) : ℝ) = ((500000000000 / 793104005649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (40932383 / 125000000) ≤ -Real.log (500000000000 / 693719127439) ∧
    -Real.log (500000000000 / 693719127439) ≤ (65491813 / 200000000) := by
  have h := checkLog_sound (w := (193719127439 / 1193719127439)) (n := 12)
    (lo := (40932383 / 125000000)) (hi := (65491813 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693719127439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693719127439 / 500000000000) = 1/(500000000000 / 693719127439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (40932383 / 125000000) (65491813 / 200000000) (Real.log (693719127439 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (693719127439 / 500000000000) = -Real.log (500000000000 / 693719127439) := by
    rw [show ((693719127439 / 500000000000) : ℝ) = ((500000000000 / 693719127439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (328097921 / 1000000000) ≤ -Real.log (500000000000 / 694162456249) ∧
    -Real.log (500000000000 / 694162456249) ≤ (164048961 / 500000000) := by
  have h := checkLog_sound (w := (194162456249 / 1194162456249)) (n := 12)
    (lo := (328097921 / 1000000000)) (hi := (164048961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694162456249 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694162456249 / 500000000000) = 1/(500000000000 / 694162456249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (328097921 / 1000000000) (164048961 / 500000000) (Real.log (694162456249 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (694162456249 / 500000000000) = -Real.log (500000000000 / 694162456249) := by
    rw [show ((694162456249 / 500000000000) : ℝ) = ((500000000000 / 694162456249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2679221 / 100000000) ≤ -Real.log (973563516351 / 1000000000000) ∧
    -Real.log (973563516351 / 1000000000000) ≤ (26792211 / 1000000000) := by
  have h := checkLog_sound (w := (26436483649 / 1973563516351)) (n := 12)
    (lo := (2679221 / 100000000)) (hi := (26792211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973563516351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973563516351) = 1/(973563516351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-26792211 / 1000000000) (-2679221 / 100000000) (Real.log (973563516351 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6672109 / 250000000) ≤ -Real.log (243416138119 / 250000000000) ∧
    -Real.log (243416138119 / 250000000000) ≤ (26688437 / 1000000000) := by
  have h := checkLog_sound (w := (6583861881 / 493416138119)) (n := 12)
    (lo := (6672109 / 250000000)) (hi := (26688437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243416138119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243416138119) = 1/(243416138119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-26688437 / 1000000000) (-6672109 / 250000000) (Real.log (243416138119 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell117
