import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0348
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

theorem reflection_log_1_neg : (106309809 / 500000000) ≤ -Real.log (5120 / 6333) ∧
    -Real.log (5120 / 6333) ≤ (212619619 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 11453)) (n := 12)
    (lo := (106309809 / 500000000)) (hi := (212619619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6333 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6333 / 5120) = 1/(5120 / 6333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (106309809 / 500000000) (212619619 / 1000000000) (Real.log (6333 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6333 / 5120) = -Real.log (5120 / 6333) := by
    rw [show ((6333 / 5120) : ℝ) = ((5120 / 6333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (135192311 / 500000000) ≤ -Real.log (3907 / 5120) ∧
    -Real.log (3907 / 5120) ≤ (270384623 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 9027)) (n := 12)
    (lo := (135192311 / 500000000)) (hi := (270384623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3907) = 1/(3907 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-270384623 / 1000000000) (-135192311 / 500000000) (Real.log (3907 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (42476547 / 200000000) ≤ -Real.log (10240 / 12663) ∧
    -Real.log (10240 / 12663) ≤ (13273921 / 62500000) := by
  have h := checkLog_sound (w := (2423 / 22903)) (n := 12)
    (lo := (42476547 / 200000000)) (hi := (13273921 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12663 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12663 / 10240) = 1/(10240 / 12663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (42476547 / 200000000) (13273921 / 62500000) (Real.log (12663 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12663 / 10240) = -Real.log (10240 / 12663) := by
    rw [show ((12663 / 10240) : ℝ) = ((10240 / 12663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (27000077 / 100000000) ≤ -Real.log (7817 / 10240) ∧
    -Real.log (7817 / 10240) ≤ (270000771 / 1000000000) := by
  have h := checkLog_sound (w := (2423 / 18057)) (n := 12)
    (lo := (27000077 / 100000000)) (hi := (270000771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7817) = 1/(7817 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-270000771 / 1000000000) (-27000077 / 100000000) (Real.log (7817 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (193931591 / 500000000) ≤ -Real.log (2560 / 3773) ∧
    -Real.log (2560 / 3773) ≤ (387863183 / 1000000000) := by
  have h := checkLog_sound (w := (1213 / 6333)) (n := 12)
    (lo := (193931591 / 500000000)) (hi := (387863183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3773 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3773 / 2560) = 1/(2560 / 3773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (193931591 / 500000000) (387863183 / 1000000000) (Real.log (3773 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3773 / 2560) = -Real.log (2560 / 3773) := by
    rw [show ((3773 / 2560) : ℝ) = ((2560 / 3773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (642127361 / 1000000000) ≤ -Real.log (1347 / 2560) ∧
    -Real.log (1347 / 2560) ≤ (321063681 / 500000000) := by
  have h := checkLog_sound (w := (1213 / 3907)) (n := 12)
    (lo := (642127361 / 1000000000)) (hi := (321063681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1347) = 1/(1347 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-321063681 / 500000000) (-642127361 / 1000000000) (Real.log (1347 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (387465541 / 1000000000) ≤ -Real.log (5120 / 7543) ∧
    -Real.log (5120 / 7543) ≤ (193732771 / 500000000) := by
  have h := checkLog_sound (w := (2423 / 12663)) (n := 12)
    (lo := (387465541 / 1000000000)) (hi := (193732771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7543 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7543 / 5120) = 1/(5120 / 7543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (387465541 / 1000000000) (193732771 / 500000000) (Real.log (7543 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7543 / 5120) = -Real.log (5120 / 7543) := by
    rw [show ((7543 / 5120) : ℝ) = ((5120 / 7543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (320507197 / 500000000) ≤ -Real.log (2697 / 5120) ∧
    -Real.log (2697 / 5120) ≤ (128202879 / 200000000) := by
  have h := checkLog_sound (w := (2423 / 7817)) (n := 12)
    (lo := (320507197 / 500000000)) (hi := (128202879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2697) = 1/(2697 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-128202879 / 200000000) (-320507197 / 500000000) (Real.log (2697 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (291239487 / 1000000000) ≤ -Real.log (200000 / 267617) ∧
    -Real.log (200000 / 267617) ≤ (4550617 / 15625000) := by
  have h := checkLog_sound (w := (67617 / 467617)) (n := 12)
    (lo := (291239487 / 1000000000)) (hi := (4550617 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267617 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(267617 / 200000) = 1/(200000 / 267617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (291239487 / 1000000000) (4550617 / 15625000) (Real.log (267617 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (267617 / 200000) = -Real.log (200000 / 267617) := by
    rw [show ((267617 / 200000) : ℝ) = ((200000 / 267617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (41261813 / 100000000) ≤ -Real.log (132383 / 200000) ∧
    -Real.log (132383 / 200000) ≤ (412618131 / 1000000000) := by
  have h := checkLog_sound (w := (67617 / 332383)) (n := 12)
    (lo := (41261813 / 100000000)) (hi := (412618131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 132383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 132383) = 1/(132383 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-412618131 / 1000000000) (-41261813 / 100000000) (Real.log (132383 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (291560043 / 1000000000) ≤ -Real.log (500000 / 669257) ∧
    -Real.log (500000 / 669257) ≤ (72890011 / 250000000) := by
  have h := checkLog_sound (w := (169257 / 1169257)) (n := 12)
    (lo := (291560043 / 1000000000)) (hi := (72890011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669257 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669257 / 500000) = 1/(500000 / 669257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (291560043 / 1000000000) (72890011 / 250000000) (Real.log (669257 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (669257 / 500000) = -Real.log (500000 / 669257) := by
    rw [show ((669257 / 500000) : ℝ) = ((500000 / 669257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (413266459 / 1000000000) ≤ -Real.log (330743 / 500000) ∧
    -Real.log (330743 / 500000) ≤ (20663323 / 50000000) := by
  have h := checkLog_sound (w := (169257 / 830743)) (n := 12)
    (lo := (413266459 / 1000000000)) (hi := (20663323 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 330743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 330743) = 1/(330743 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-20663323 / 50000000) (-413266459 / 1000000000) (Real.log (330743 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (220637213 / 1000000000) ≤ -Real.log (1000000 / 1246871) ∧
    -Real.log (1000000 / 1246871) ≤ (110318607 / 500000000) := by
  have h := checkLog_sound (w := (246871 / 2246871)) (n := 12)
    (lo := (220637213 / 1000000000)) (hi := (110318607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1246871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1246871 / 1000000) = 1/(1000000 / 1246871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (220637213 / 1000000000) (110318607 / 500000000) (Real.log (1246871 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1246871 / 1000000) = -Real.log (1000000 / 1246871) := by
    rw [show ((1246871 / 1000000) : ℝ) = ((1000000 / 1246871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (283518751 / 1000000000) ≤ -Real.log (753129 / 1000000) ∧
    -Real.log (753129 / 1000000) ≤ (8859961 / 31250000) := by
  have h := checkLog_sound (w := (246871 / 1753129)) (n := 12)
    (lo := (283518751 / 1000000000)) (hi := (8859961 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 753129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 753129) = 1/(753129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-8859961 / 31250000) (-283518751 / 1000000000) (Real.log (753129 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (220905047 / 1000000000) ≤ -Real.log (200000 / 249441) ∧
    -Real.log (200000 / 249441) ≤ (27613131 / 125000000) := by
  have h := checkLog_sound (w := (49441 / 449441)) (n := 12)
    (lo := (220905047 / 1000000000)) (hi := (27613131 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249441 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249441 / 200000) = 1/(200000 / 249441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (220905047 / 1000000000) (27613131 / 125000000) (Real.log (249441 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (249441 / 200000) = -Real.log (200000 / 249441) := by
    rw [show ((249441 / 200000) : ℝ) = ((200000 / 249441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (70990583 / 250000000) ≤ -Real.log (150559 / 200000) ∧
    -Real.log (150559 / 200000) ≤ (283962333 / 1000000000) := by
  have h := checkLog_sound (w := (49441 / 350559)) (n := 12)
    (lo := (70990583 / 250000000)) (hi := (283962333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 150559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 150559) = 1/(150559 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-283962333 / 1000000000) (-70990583 / 250000000) (Real.log (150559 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (43991101 / 62500000) ≤ -Real.log (7812500000 / 15793249983) ∧
    -Real.log (7812500000 / 15793249983) ≤ (351928809 / 500000000) := by
  have h := checkLog_sound (w := (168249983 / 31418249983)) (n := 12)
    (lo := (2677609 / 250000000)) (hi := (10710437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15793249983 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15793249983 / 15625000000) = 1/(7812500000 / 15793249983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (43991101 / 62500000) (351928809 / 500000000) (Real.log (15793249983 / 7812500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (15793249983 / 7812500000) = -Real.log (7812500000 / 15793249983) := by
    rw [show ((15793249983 / 7812500000) : ℝ) = ((7812500000 / 15793249983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (352413251 / 500000000) ≤ -Real.log (500000000000 / 1011747792093) ∧
    -Real.log (500000000000 / 1011747792093) ≤ (88103313 / 125000000) := by
  have h := checkLog_sound (w := (11747792093 / 2011747792093)) (n := 12)
    (lo := (5839661 / 500000000)) (hi := (11679323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1011747792093 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1011747792093 / 1000000000000) = 1/(500000000000 / 1011747792093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (352413251 / 500000000) (88103313 / 125000000) (Real.log (1011747792093 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1011747792093 / 500000000000) = -Real.log (500000000000 / 1011747792093) := by
    rw [show ((1011747792093 / 500000000000) : ℝ) = ((500000000000 / 1011747792093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (126038991 / 250000000) ≤ -Real.log (125000000000 / 206948444423) ∧
    -Real.log (125000000000 / 206948444423) ≤ (100831193 / 200000000) := by
  have h := checkLog_sound (w := (81948444423 / 331948444423)) (n := 12)
    (lo := (126038991 / 250000000)) (hi := (100831193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206948444423 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(206948444423 / 125000000000) = 1/(125000000000 / 206948444423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (126038991 / 250000000) (100831193 / 200000000) (Real.log (206948444423 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (206948444423 / 125000000000) = -Real.log (125000000000 / 206948444423) := by
    rw [show ((206948444423 / 125000000000) : ℝ) = ((125000000000 / 206948444423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (25243369 / 50000000) ≤ -Real.log (250000000000 / 414191446543) ∧
    -Real.log (250000000000 / 414191446543) ≤ (504867381 / 1000000000) := by
  have h := checkLog_sound (w := (164191446543 / 664191446543)) (n := 12)
    (lo := (25243369 / 50000000)) (hi := (504867381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414191446543 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414191446543 / 250000000000) = 1/(250000000000 / 414191446543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (25243369 / 50000000) (504867381 / 1000000000) (Real.log (414191446543 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (414191446543 / 250000000000) = -Real.log (250000000000 / 414191446543) := by
    rw [show ((414191446543 / 250000000000) : ℝ) = ((250000000000 / 414191446543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0348
