import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell001
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

theorem reflection_log_1_neg : (56020153 / 250000000) ≤ -Real.log (2560 / 3203) ∧
    -Real.log (2560 / 3203) ≤ (224080613 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 5763)) (n := 12)
    (lo := (56020153 / 250000000)) (hi := (224080613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3203 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3203 / 2560) = 1/(2560 / 3203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (56020153 / 250000000) (224080613 / 1000000000) (Real.log (3203 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3203 / 2560) = -Real.log (2560 / 3203) := by
    rw [show ((3203 / 2560) : ℝ) = ((2560 / 3203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (144622897 / 500000000) ≤ -Real.log (1917 / 2560) ∧
    -Real.log (1917 / 2560) ≤ (57849159 / 200000000) := by
  have h := checkLog_sound (w := (643 / 4477)) (n := 12)
    (lo := (144622897 / 500000000)) (hi := (57849159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1917) = 1/(1917 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-57849159 / 200000000) (-144622897 / 500000000) (Real.log (1917 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (223612191 / 1000000000) ≤ -Real.log (5120 / 6403) ∧
    -Real.log (5120 / 6403) ≤ (6987881 / 31250000) := by
  have h := checkLog_sound (w := (1283 / 11523)) (n := 12)
    (lo := (223612191 / 1000000000)) (hi := (6987881 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6403 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6403 / 5120) = 1/(5120 / 6403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (223612191 / 1000000000) (6987881 / 31250000) (Real.log (6403 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6403 / 5120) = -Real.log (5120 / 6403) := by
    rw [show ((6403 / 5120) : ℝ) = ((5120 / 6403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (288463627 / 1000000000) ≤ -Real.log (3837 / 5120) ∧
    -Real.log (3837 / 5120) ≤ (72115907 / 250000000) := by
  have h := checkLog_sound (w := (1283 / 8957)) (n := 12)
    (lo := (288463627 / 1000000000)) (hi := (72115907 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3837) = 1/(3837 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-72115907 / 250000000) (-288463627 / 1000000000) (Real.log (3837 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (81767681 / 500000000) ≤ -Real.log (1000000 / 1177667) ∧
    -Real.log (1000000 / 1177667) ≤ (163535363 / 1000000000) := by
  have h := checkLog_sound (w := (177667 / 2177667)) (n := 12)
    (lo := (81767681 / 500000000)) (hi := (163535363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1177667 / 1000000) = 1/(1000000 / 1177667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (81767681 / 500000000) (163535363 / 1000000000) (Real.log (1177667 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1177667 / 1000000) = -Real.log (1000000 / 1177667) := by
    rw [show ((1177667 / 1000000) : ℝ) = ((1000000 / 1177667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (764101 / 3906250) ≤ -Real.log (822333 / 1000000) ∧
    -Real.log (822333 / 1000000) ≤ (195609857 / 1000000000) := by
  have h := checkLog_sound (w := (177667 / 1822333)) (n := 12)
    (lo := (764101 / 3906250)) (hi := (195609857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 822333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 822333) = 1/(822333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-195609857 / 1000000000) (-764101 / 3906250) (Real.log (822333 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (81945119 / 500000000) ≤ -Real.log (200000 / 235617) ∧
    -Real.log (200000 / 235617) ≤ (163890239 / 1000000000) := by
  have h := checkLog_sound (w := (35617 / 435617)) (n := 12)
    (lo := (81945119 / 500000000)) (hi := (163890239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235617 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235617 / 200000) = 1/(200000 / 235617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (81945119 / 500000000) (163890239 / 1000000000) (Real.log (235617 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (235617 / 200000) = -Real.log (200000 / 235617) := by
    rw [show ((235617 / 200000) : ℝ) = ((200000 / 235617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (39223659 / 200000000) ≤ -Real.log (164383 / 200000) ∧
    -Real.log (164383 / 200000) ≤ (24514787 / 125000000) := by
  have h := checkLog_sound (w := (35617 / 364383)) (n := 12)
    (lo := (39223659 / 200000000)) (hi := (24514787 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 164383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 164383) = 1/(164383 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-24514787 / 125000000) (-39223659 / 200000000) (Real.log (164383 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (29831683 / 250000000) ≤ -Real.log (500000 / 563369) ∧
    -Real.log (500000 / 563369) ≤ (119326733 / 1000000000) := by
  have h := checkLog_sound (w := (63369 / 1063369)) (n := 12)
    (lo := (29831683 / 250000000)) (hi := (119326733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((563369 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(563369 / 500000) = 1/(500000 / 563369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (29831683 / 250000000) (119326733 / 1000000000) (Real.log (563369 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (563369 / 500000) = -Real.log (500000 / 563369) := by
    rw [show ((563369 / 500000) : ℝ) = ((500000 / 563369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (135519653 / 1000000000) ≤ -Real.log (436631 / 500000) ∧
    -Real.log (436631 / 500000) ≤ (67759827 / 500000000) := by
  have h := checkLog_sound (w := (63369 / 936631)) (n := 12)
    (lo := (135519653 / 1000000000)) (hi := (67759827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 436631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 436631) = 1/(436631 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-67759827 / 500000000) (-135519653 / 1000000000) (Real.log (436631 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (119596501 / 1000000000) ≤ -Real.log (500000 / 563521) ∧
    -Real.log (500000 / 563521) ≤ (59798251 / 500000000) := by
  have h := checkLog_sound (w := (63521 / 1063521)) (n := 12)
    (lo := (119596501 / 1000000000)) (hi := (59798251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((563521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(563521 / 500000) = 1/(500000 / 563521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (119596501 / 1000000000) (59798251 / 500000000) (Real.log (563521 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (563521 / 500000) = -Real.log (500000 / 563521) := by
    rw [show ((563521 / 500000) : ℝ) = ((500000 / 563521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (67933917 / 500000000) ≤ -Real.log (436479 / 500000) ∧
    -Real.log (436479 / 500000) ≤ (27173567 / 200000000) := by
  have h := checkLog_sound (w := (63521 / 936479)) (n := 12)
    (lo := (67933917 / 500000000)) (hi := (27173567 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 436479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 436479) = 1/(436479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-27173567 / 200000000) (-67933917 / 500000000) (Real.log (436479 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (512075819 / 1000000000) ≤ -Real.log (250000000000 / 417187907219) ∧
    -Real.log (250000000000 / 417187907219) ≤ (25603791 / 50000000) := by
  have h := checkLog_sound (w := (167187907219 / 667187907219)) (n := 12)
    (lo := (512075819 / 1000000000)) (hi := (25603791 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417187907219 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417187907219 / 250000000000) = 1/(250000000000 / 417187907219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (512075819 / 1000000000) (25603791 / 50000000) (Real.log (417187907219 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (417187907219 / 250000000000) = -Real.log (250000000000 / 417187907219) := by
    rw [show ((417187907219 / 250000000000) : ℝ) = ((250000000000 / 417187907219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (256663203 / 500000000) ≤ -Real.log (50000000000 / 83541992697) ∧
    -Real.log (50000000000 / 83541992697) ≤ (513326407 / 1000000000) := by
  have h := checkLog_sound (w := (33541992697 / 133541992697)) (n := 12)
    (lo := (256663203 / 500000000)) (hi := (513326407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83541992697 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83541992697 / 50000000000) = 1/(50000000000 / 83541992697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (256663203 / 500000000) (513326407 / 1000000000) (Real.log (83541992697 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (83541992697 / 50000000000) = -Real.log (50000000000 / 83541992697) := by
    rw [show ((83541992697 / 50000000000) : ℝ) = ((50000000000 / 83541992697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (359145219 / 1000000000) ≤ -Real.log (31250000000 / 44753273613) ∧
    -Real.log (31250000000 / 44753273613) ≤ (17957261 / 50000000) := by
  have h := checkLog_sound (w := (13503273613 / 76003273613)) (n := 12)
    (lo := (359145219 / 1000000000)) (hi := (17957261 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44753273613 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44753273613 / 31250000000) = 1/(31250000000 / 44753273613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (359145219 / 1000000000) (17957261 / 50000000) (Real.log (44753273613 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (44753273613 / 31250000000) = -Real.log (31250000000 / 44753273613) := by
    rw [show ((44753273613 / 31250000000) : ℝ) = ((31250000000 / 44753273613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (180004267 / 500000000) ≤ -Real.log (250000000000 / 358335411813) ∧
    -Real.log (250000000000 / 358335411813) ≤ (72001707 / 200000000) := by
  have h := checkLog_sound (w := (108335411813 / 608335411813)) (n := 12)
    (lo := (180004267 / 500000000)) (hi := (72001707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358335411813 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358335411813 / 250000000000) = 1/(250000000000 / 358335411813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (180004267 / 500000000) (72001707 / 200000000) (Real.log (358335411813 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (358335411813 / 250000000000) = -Real.log (250000000000 / 358335411813) := by
    rw [show ((358335411813 / 250000000000) : ℝ) = ((250000000000 / 358335411813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (127423193 / 500000000) ≤ -Real.log (500000000000 / 645131701597) ∧
    -Real.log (500000000000 / 645131701597) ≤ (254846387 / 1000000000) := by
  have h := checkLog_sound (w := (145131701597 / 1145131701597)) (n := 12)
    (lo := (127423193 / 500000000)) (hi := (254846387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((645131701597 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(645131701597 / 500000000000) = 1/(500000000000 / 645131701597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (127423193 / 500000000) (254846387 / 1000000000) (Real.log (645131701597 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (645131701597 / 500000000000) = -Real.log (500000000000 / 645131701597) := by
    rw [show ((645131701597 / 500000000000) : ℝ) = ((500000000000 / 645131701597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (51092867 / 200000000) ≤ -Real.log (488281250 / 630400863) ∧
    -Real.log (488281250 / 630400863) ≤ (15966521 / 62500000) := by
  have h := checkLog_sound (w := (142119613 / 1118682113)) (n := 12)
    (lo := (51092867 / 200000000)) (hi := (15966521 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630400863 / 488281250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630400863 / 488281250) = 1/(488281250 / 630400863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (51092867 / 200000000) (15966521 / 62500000) (Real.log (630400863 / 488281250)) := by
  have h := reflection_log_18_neg
  have he : Real.log (630400863 / 488281250) = -Real.log (488281250 / 630400863) := by
    rw [show ((630400863 / 488281250) : ℝ) = ((488281250 / 630400863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4067833 / 250000000) ≤ -Real.log (245965082559 / 250000000000) ∧
    -Real.log (245965082559 / 250000000000) ≤ (16271333 / 1000000000) := by
  have h := checkLog_sound (w := (4034917441 / 495965082559)) (n := 12)
    (lo := (4067833 / 250000000)) (hi := (16271333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245965082559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245965082559) = 1/(245965082559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16271333 / 1000000000) (-4067833 / 250000000) (Real.log (245965082559 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16192921 / 1000000000) ≤ -Real.log (245984369839 / 250000000000) ∧
    -Real.log (245984369839 / 250000000000) ≤ (8096461 / 500000000) := by
  have h := checkLog_sound (w := (4015630161 / 495984369839)) (n := 12)
    (lo := (16192921 / 1000000000)) (hi := (8096461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245984369839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245984369839) = 1/(245984369839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8096461 / 500000000) (-16192921 / 1000000000) (Real.log (245984369839 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell001
