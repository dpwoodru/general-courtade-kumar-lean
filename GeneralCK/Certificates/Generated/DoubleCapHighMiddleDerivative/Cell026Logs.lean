import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell026
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

theorem reflection_log_1_neg : (11786019 / 50000000) ≤ -Real.log (5120 / 6481) ∧
    -Real.log (5120 / 6481) ≤ (235720381 / 1000000000) := by
  have h := checkLog_sound (w := (1361 / 11601)) (n := 12)
    (lo := (11786019 / 50000000)) (hi := (235720381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6481 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6481 / 5120) = 1/(5120 / 6481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11786019 / 50000000) (235720381 / 1000000000) (Real.log (6481 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6481 / 5120) = -Real.log (5120 / 6481) := by
    rw [show ((6481 / 5120) : ℝ) = ((5120 / 6481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (154500737 / 500000000) ≤ -Real.log (3759 / 5120) ∧
    -Real.log (3759 / 5120) ≤ (12360059 / 40000000) := by
  have h := checkLog_sound (w := (1361 / 8879)) (n := 12)
    (lo := (154500737 / 500000000)) (hi := (12360059 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3759) = 1/(3759 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12360059 / 40000000) (-154500737 / 500000000) (Real.log (3759 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (235257381 / 1000000000) ≤ -Real.log (2560 / 3239) ∧
    -Real.log (2560 / 3239) ≤ (117628691 / 500000000) := by
  have h := checkLog_sound (w := (679 / 5799)) (n := 12)
    (lo := (235257381 / 1000000000)) (hi := (117628691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3239 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3239 / 2560) = 1/(2560 / 3239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (235257381 / 1000000000) (117628691 / 500000000) (Real.log (3239 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3239 / 2560) = -Real.log (2560 / 3239) := by
    rw [show ((3239 / 2560) : ℝ) = ((2560 / 3239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (77050927 / 250000000) ≤ -Real.log (1881 / 2560) ∧
    -Real.log (1881 / 2560) ≤ (308203709 / 1000000000) := by
  have h := checkLog_sound (w := (679 / 4441)) (n := 12)
    (lo := (77050927 / 250000000)) (hi := (308203709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1881) = 1/(1881 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-308203709 / 1000000000) (-77050927 / 250000000) (Real.log (1881 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (172368017 / 1000000000) ≤ -Real.log (200000 / 237623) ∧
    -Real.log (200000 / 237623) ≤ (86184009 / 500000000) := by
  have h := checkLog_sound (w := (37623 / 437623)) (n := 12)
    (lo := (172368017 / 1000000000)) (hi := (86184009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237623 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237623 / 200000) = 1/(200000 / 237623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (172368017 / 1000000000) (86184009 / 500000000) (Real.log (237623 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (237623 / 200000) = -Real.log (200000 / 237623) := by
    rw [show ((237623 / 200000) : ℝ) = ((200000 / 237623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (104198287 / 500000000) ≤ -Real.log (162377 / 200000) ∧
    -Real.log (162377 / 200000) ≤ (8335863 / 40000000) := by
  have h := checkLog_sound (w := (37623 / 362377)) (n := 12)
    (lo := (104198287 / 500000000)) (hi := (8335863 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 162377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 162377) = 1/(162377 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-8335863 / 40000000) (-104198287 / 500000000) (Real.log (162377 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (86360307 / 500000000) ≤ -Real.log (500000 / 594267) ∧
    -Real.log (500000 / 594267) ≤ (34544123 / 200000000) := by
  have h := checkLog_sound (w := (94267 / 1094267)) (n := 12)
    (lo := (86360307 / 500000000)) (hi := (34544123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594267 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(594267 / 500000) = 1/(500000 / 594267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (86360307 / 500000000) (34544123 / 200000000) (Real.log (594267 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (594267 / 500000) = -Real.log (500000 / 594267) := by
    rw [show ((594267 / 500000) : ℝ) = ((500000 / 594267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (20891279 / 100000000) ≤ -Real.log (405733 / 500000) ∧
    -Real.log (405733 / 500000) ≤ (208912791 / 1000000000) := by
  have h := checkLog_sound (w := (94267 / 905733)) (n := 12)
    (lo := (20891279 / 100000000)) (hi := (208912791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 405733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 405733) = 1/(405733 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-208912791 / 1000000000) (-20891279 / 100000000) (Real.log (405733 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (7877911 / 62500000) ≤ -Real.log (200000 / 226867) ∧
    -Real.log (200000 / 226867) ≤ (126046577 / 1000000000) := by
  have h := checkLog_sound (w := (26867 / 426867)) (n := 12)
    (lo := (7877911 / 62500000)) (hi := (126046577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226867 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226867 / 200000) = 1/(200000 / 226867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (7877911 / 62500000) (126046577 / 1000000000) (Real.log (226867 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (226867 / 200000) = -Real.log (200000 / 226867) := by
    rw [show ((226867 / 200000) : ℝ) = ((200000 / 226867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (144257281 / 1000000000) ≤ -Real.log (173133 / 200000) ∧
    -Real.log (173133 / 200000) ≤ (72128641 / 500000000) := by
  have h := checkLog_sound (w := (26867 / 373133)) (n := 12)
    (lo := (144257281 / 1000000000)) (hi := (72128641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173133) = 1/(173133 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-72128641 / 500000000) (-144257281 / 1000000000) (Real.log (173133 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (6315771 / 50000000) ≤ -Real.log (12500 / 14183) ∧
    -Real.log (12500 / 14183) ≤ (126315421 / 1000000000) := by
  have h := checkLog_sound (w := (1683 / 26683)) (n := 12)
    (lo := (6315771 / 50000000)) (hi := (126315421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14183 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14183 / 12500) = 1/(12500 / 14183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (6315771 / 50000000) (126315421 / 1000000000) (Real.log (14183 / 12500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (14183 / 12500) = -Real.log (12500 / 14183) := by
    rw [show ((14183 / 12500) : ℝ) = ((12500 / 14183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (144609673 / 1000000000) ≤ -Real.log (10817 / 12500) ∧
    -Real.log (10817 / 12500) ≤ (72304837 / 500000000) := by
  have h := checkLog_sound (w := (1683 / 23317)) (n := 12)
    (lo := (144609673 / 1000000000)) (hi := (72304837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 10817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 10817) = 1/(10817 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-72304837 / 500000000) (-144609673 / 1000000000) (Real.log (10817 / 12500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (543461089 / 1000000000) ≤ -Real.log (500000000000 / 860978203083) ∧
    -Real.log (500000000000 / 860978203083) ≤ (54346109 / 100000000) := by
  have h := checkLog_sound (w := (360978203083 / 1360978203083)) (n := 12)
    (lo := (543461089 / 1000000000)) (hi := (54346109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((860978203083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(860978203083 / 500000000000) = 1/(500000000000 / 860978203083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (543461089 / 1000000000) (54346109 / 100000000) (Real.log (860978203083 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (860978203083 / 500000000000) = -Real.log (500000000000 / 860978203083) := by
    rw [show ((860978203083 / 500000000000) : ℝ) = ((500000000000 / 860978203083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (272360927 / 500000000) ≤ -Real.log (20000000000 / 34482575153) ∧
    -Real.log (20000000000 / 34482575153) ≤ (108944371 / 200000000) := by
  have h := checkLog_sound (w := (14482575153 / 54482575153)) (n := 12)
    (lo := (272360927 / 500000000)) (hi := (108944371 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34482575153 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34482575153 / 20000000000) = 1/(20000000000 / 34482575153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (272360927 / 500000000) (108944371 / 200000000) (Real.log (34482575153 / 20000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (34482575153 / 20000000000) = -Real.log (20000000000 / 34482575153) := by
    rw [show ((34482575153 / 20000000000) : ℝ) = ((20000000000 / 34482575153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (23797787 / 62500000) ≤ -Real.log (125000000000 / 182925383521) ∧
    -Real.log (125000000000 / 182925383521) ≤ (380764593 / 1000000000) := by
  have h := checkLog_sound (w := (57925383521 / 307925383521)) (n := 12)
    (lo := (23797787 / 62500000)) (hi := (380764593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182925383521 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182925383521 / 125000000000) = 1/(125000000000 / 182925383521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (23797787 / 62500000) (380764593 / 1000000000) (Real.log (182925383521 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (182925383521 / 125000000000) = -Real.log (125000000000 / 182925383521) := by
    rw [show ((182925383521 / 125000000000) : ℝ) = ((125000000000 / 182925383521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (76326681 / 200000000) ≤ -Real.log (25000000000 / 36616876123) ∧
    -Real.log (25000000000 / 36616876123) ≤ (190816703 / 500000000) := by
  have h := checkLog_sound (w := (11616876123 / 61616876123)) (n := 12)
    (lo := (76326681 / 200000000)) (hi := (190816703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36616876123 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36616876123 / 25000000000) = 1/(25000000000 / 36616876123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (76326681 / 200000000) (190816703 / 500000000) (Real.log (36616876123 / 25000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (36616876123 / 25000000000) = -Real.log (25000000000 / 36616876123) := by
    rw [show ((36616876123 / 25000000000) : ℝ) = ((25000000000 / 36616876123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (270303857 / 1000000000) ≤ -Real.log (500000000000 / 655181276821) ∧
    -Real.log (500000000000 / 655181276821) ≤ (135151929 / 500000000) := by
  have h := checkLog_sound (w := (155181276821 / 1155181276821)) (n := 12)
    (lo := (270303857 / 1000000000)) (hi := (135151929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655181276821 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655181276821 / 500000000000) = 1/(500000000000 / 655181276821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (270303857 / 1000000000) (135151929 / 500000000) (Real.log (655181276821 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (655181276821 / 500000000000) = -Real.log (500000000000 / 655181276821) := by
    rw [show ((655181276821 / 500000000000) : ℝ) = ((500000000000 / 655181276821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (270925093 / 1000000000) ≤ -Real.log (500000000000 / 655588425627) ∧
    -Real.log (500000000000 / 655588425627) ≤ (135462547 / 500000000) := by
  have h := checkLog_sound (w := (155588425627 / 1155588425627)) (n := 12)
    (lo := (270925093 / 1000000000)) (hi := (135462547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655588425627 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655588425627 / 500000000000) = 1/(500000000000 / 655588425627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (270925093 / 1000000000) (135462547 / 500000000) (Real.log (655588425627 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (655588425627 / 500000000000) = -Real.log (500000000000 / 655588425627) := by
    rw [show ((655588425627 / 500000000000) : ℝ) = ((500000000000 / 655588425627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (18294253 / 1000000000) ≤ -Real.log (153417511 / 156250000) ∧
    -Real.log (153417511 / 156250000) ≤ (9147127 / 500000000) := by
  have h := checkLog_sound (w := (2832489 / 309667511)) (n := 12)
    (lo := (18294253 / 1000000000)) (hi := (9147127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 153417511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 153417511) = 1/(153417511 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9147127 / 500000000) (-18294253 / 1000000000) (Real.log (153417511 / 156250000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3642141 / 200000000) ≤ -Real.log (39278164311 / 40000000000) ∧
    -Real.log (39278164311 / 40000000000) ≤ (9105353 / 500000000) := by
  have h := checkLog_sound (w := (721835689 / 79278164311)) (n := 12)
    (lo := (3642141 / 200000000)) (hi := (9105353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39278164311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39278164311) = 1/(39278164311 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-9105353 / 500000000) (-3642141 / 200000000) (Real.log (39278164311 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell026
