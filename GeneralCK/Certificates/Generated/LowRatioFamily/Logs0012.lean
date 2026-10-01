import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_768_neg : (156976809 / 500000000) ≤ -Real.log (250000000000 / 342206561649) ∧
    -Real.log (250000000000 / 342206561649) ≤ (313953619 / 1000000000) := by
  have h := checkLog_sound (w := (92206561649 / 592206561649)) (n := 12)
    (lo := (156976809 / 500000000)) (hi := (313953619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342206561649 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342206561649 / 250000000000) = 1/(250000000000 / 342206561649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_768 : Bounds (156976809 / 500000000) (313953619 / 1000000000) (Real.log (342206561649 / 250000000000)) := by
  have h := reflection_log_768_neg
  have he : Real.log (342206561649 / 250000000000) = -Real.log (250000000000 / 342206561649) := by
    rw [show ((342206561649 / 250000000000) : ℝ) = ((250000000000 / 342206561649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_769_neg : (18099093 / 125000000) ≤ -Real.log (5000 / 5779) ∧
    -Real.log (5000 / 5779) ≤ (28958549 / 200000000) := by
  have h := checkLog_sound (w := (779 / 10779)) (n := 12)
    (lo := (18099093 / 125000000)) (hi := (28958549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5779 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5779 / 5000) = 1/(5000 / 5779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_769 : Bounds (18099093 / 125000000) (28958549 / 200000000) (Real.log (5779 / 5000)) := by
  have h := reflection_log_769_neg
  have he : Real.log (5779 / 5000) = -Real.log (5000 / 5779) := by
    rw [show ((5779 / 5000) : ℝ) = ((5000 / 5779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_770_neg : (33873169 / 200000000) ≤ -Real.log (4221 / 5000) ∧
    -Real.log (4221 / 5000) ≤ (84682923 / 500000000) := by
  have h := checkLog_sound (w := (779 / 9221)) (n := 12)
    (lo := (33873169 / 200000000)) (hi := (84682923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4221) = 1/(4221 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_770 : Bounds (-84682923 / 500000000) (-33873169 / 200000000) (Real.log (4221 / 5000)) := by
  have h := reflection_log_770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_771_neg : (155787 / 1000000000) ≤ -Real.log (5000000 / 5000779) ∧
    -Real.log (5000000 / 5000779) ≤ (38947 / 250000000) := by
  have h := checkLog_sound (w := (779 / 10000779)) (n := 12)
    (lo := (155787 / 1000000000)) (hi := (38947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000779 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000779 / 5000000) = 1/(5000000 / 5000779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_771 : Bounds (155787 / 1000000000) (38947 / 250000000) (Real.log (5000779 / 5000000)) := by
  have h := reflection_log_771_neg
  have he : Real.log (5000779 / 5000000) = -Real.log (5000000 / 5000779) := by
    rw [show ((5000779 / 5000000) : ℝ) = ((5000000 / 5000779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_772_neg : (38953 / 250000000) ≤ -Real.log (4999221 / 5000000) ∧
    -Real.log (4999221 / 5000000) ≤ (155813 / 1000000000) := by
  have h := checkLog_sound (w := (779 / 9999221)) (n := 12)
    (lo := (38953 / 250000000)) (hi := (155813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999221) = 1/(4999221 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_772 : Bounds (-155813 / 1000000000) (-38953 / 250000000) (Real.log (4999221 / 5000000)) := by
  have h := reflection_log_772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_773_neg : (15042829 / 200000000) ≤ -Real.log (200000 / 215623) ∧
    -Real.log (200000 / 215623) ≤ (37607073 / 500000000) := by
  have h := checkLog_sound (w := (15623 / 415623)) (n := 12)
    (lo := (15042829 / 200000000)) (hi := (37607073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215623 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215623 / 200000) = 1/(200000 / 215623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_773 : Bounds (15042829 / 200000000) (37607073 / 500000000) (Real.log (215623 / 200000)) := by
  have h := reflection_log_773_neg
  have he : Real.log (215623 / 200000) = -Real.log (200000 / 215623) := by
    rw [show ((215623 / 200000) : ℝ) = ((200000 / 215623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_774_neg : (10166849 / 125000000) ≤ -Real.log (184377 / 200000) ∧
    -Real.log (184377 / 200000) ≤ (81334793 / 1000000000) := by
  have h := checkLog_sound (w := (15623 / 384377)) (n := 12)
    (lo := (10166849 / 125000000)) (hi := (81334793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184377) = 1/(184377 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_774 : Bounds (-81334793 / 1000000000) (-10166849 / 125000000) (Real.log (184377 / 200000)) := by
  have h := reflection_log_774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_775_neg : (75405201 / 1000000000) ≤ -Real.log (1000000 / 1078321) ∧
    -Real.log (1000000 / 1078321) ≤ (37702601 / 500000000) := by
  have h := checkLog_sound (w := (78321 / 2078321)) (n := 12)
    (lo := (75405201 / 1000000000)) (hi := (37702601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078321 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078321 / 1000000) = 1/(1000000 / 1078321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_775 : Bounds (75405201 / 1000000000) (37702601 / 500000000) (Real.log (1078321 / 1000000)) := by
  have h := reflection_log_775_neg
  have he : Real.log (1078321 / 1000000) = -Real.log (1000000 / 1078321) := by
    rw [show ((1078321 / 1000000) : ℝ) = ((1000000 / 1078321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_776_neg : (318587 / 3906250) ≤ -Real.log (921679 / 1000000) ∧
    -Real.log (921679 / 1000000) ≤ (81558273 / 1000000000) := by
  have h := checkLog_sound (w := (78321 / 1921679)) (n := 12)
    (lo := (318587 / 3906250)) (hi := (81558273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921679) = 1/(921679 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_776 : Bounds (-81558273 / 1000000000) (-318587 / 3906250) (Real.log (921679 / 1000000)) := by
  have h := reflection_log_776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_777_neg : (615307 / 100000000) ≤ -Real.log (993865820959 / 1000000000000) ∧
    -Real.log (993865820959 / 1000000000000) ≤ (6153071 / 1000000000) := by
  have h := checkLog_sound (w := (6134179041 / 1993865820959)) (n := 12)
    (lo := (615307 / 100000000)) (hi := (6153071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993865820959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993865820959) = 1/(993865820959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_777 : Bounds (-6153071 / 1000000000) (-615307 / 100000000) (Real.log (993865820959 / 1000000000000)) := by
  have h := reflection_log_777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_778_neg : (3060323 / 500000000) ≤ -Real.log (39755921871 / 40000000000) ∧
    -Real.log (39755921871 / 40000000000) ≤ (6120647 / 1000000000) := by
  have h := checkLog_sound (w := (244078129 / 79755921871)) (n := 12)
    (lo := (3060323 / 500000000)) (hi := (6120647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39755921871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39755921871) = 1/(39755921871 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_778 : Bounds (-6120647 / 1000000000) (-3060323 / 500000000) (Real.log (39755921871 / 40000000000)) := by
  have h := reflection_log_778_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_779_neg : (156548937 / 1000000000) ≤ -Real.log (100000000000 / 116946799221) ∧
    -Real.log (100000000000 / 116946799221) ≤ (78274469 / 500000000) := by
  have h := checkLog_sound (w := (16946799221 / 216946799221)) (n := 12)
    (lo := (156548937 / 1000000000)) (hi := (78274469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116946799221 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116946799221 / 100000000000) = 1/(100000000000 / 116946799221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_779 : Bounds (156548937 / 1000000000) (78274469 / 500000000) (Real.log (116946799221 / 100000000000)) := by
  have h := reflection_log_779_neg
  have he : Real.log (116946799221 / 100000000000) = -Real.log (100000000000 / 116946799221) := by
    rw [show ((116946799221 / 100000000000) : ℝ) = ((100000000000 / 116946799221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_780_neg : (78481737 / 500000000) ≤ -Real.log (500000000000 / 584976439737) ∧
    -Real.log (500000000000 / 584976439737) ≤ (6278539 / 40000000) := by
  have h := checkLog_sound (w := (84976439737 / 1084976439737)) (n := 12)
    (lo := (78481737 / 500000000)) (hi := (6278539 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584976439737 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584976439737 / 500000000000) = 1/(500000000000 / 584976439737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_780 : Bounds (78481737 / 500000000) (6278539 / 40000000) (Real.log (584976439737 / 500000000000)) := by
  have h := reflection_log_780_neg
  have he : Real.log (584976439737 / 500000000000) = -Real.log (500000000000 / 584976439737) := by
    rw [show ((584976439737 / 500000000000) : ℝ) = ((500000000000 / 584976439737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_781_neg : (156976809 / 500000000) ≤ -Real.log (500000000000 / 684413123297) ∧
    -Real.log (500000000000 / 684413123297) ≤ (313953619 / 1000000000) := by
  have h := checkLog_sound (w := (184413123297 / 1184413123297)) (n := 12)
    (lo := (156976809 / 500000000)) (hi := (313953619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684413123297 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684413123297 / 500000000000) = 1/(500000000000 / 684413123297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_781 : Bounds (156976809 / 500000000) (313953619 / 1000000000) (Real.log (684413123297 / 500000000000)) := by
  have h := reflection_log_781_neg
  have he : Real.log (684413123297 / 500000000000) = -Real.log (500000000000 / 684413123297) := by
    rw [show ((684413123297 / 500000000000) : ℝ) = ((500000000000 / 684413123297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_782_neg : (31415859 / 100000000) ≤ -Real.log (195312500 / 267403681) ∧
    -Real.log (195312500 / 267403681) ≤ (314158591 / 1000000000) := by
  have h := checkLog_sound (w := (72091181 / 462716181)) (n := 12)
    (lo := (31415859 / 100000000)) (hi := (314158591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267403681 / 195312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(267403681 / 195312500) = 1/(195312500 / 267403681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_782 : Bounds (31415859 / 100000000) (314158591 / 1000000000) (Real.log (267403681 / 195312500)) := by
  have h := reflection_log_782_neg
  have he : Real.log (267403681 / 195312500) = -Real.log (195312500 / 267403681) := by
    rw [show ((267403681 / 195312500) : ℝ) = ((195312500 / 267403681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_783_neg : (144879261 / 1000000000) ≤ -Real.log (10000 / 11559) ∧
    -Real.log (10000 / 11559) ≤ (72439631 / 500000000) := by
  have h := checkLog_sound (w := (1559 / 21559)) (n := 12)
    (lo := (144879261 / 1000000000)) (hi := (72439631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11559 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11559 / 10000) = 1/(10000 / 11559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_783 : Bounds (144879261 / 1000000000) (72439631 / 500000000) (Real.log (11559 / 10000)) := by
  have h := reflection_log_783_neg
  have he : Real.log (11559 / 10000) = -Real.log (10000 / 11559) := by
    rw [show ((11559 / 10000) : ℝ) = ((10000 / 11559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_784_neg : (169484307 / 1000000000) ≤ -Real.log (8441 / 10000) ∧
    -Real.log (8441 / 10000) ≤ (42371077 / 250000000) := by
  have h := checkLog_sound (w := (1559 / 18441)) (n := 12)
    (lo := (169484307 / 1000000000)) (hi := (42371077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8441) = 1/(8441 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_784 : Bounds (-42371077 / 250000000) (-169484307 / 1000000000) (Real.log (8441 / 10000)) := by
  have h := reflection_log_784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_785_neg : (155887 / 1000000000) ≤ -Real.log (10000000 / 10001559) ∧
    -Real.log (10000000 / 10001559) ≤ (9743 / 62500000) := by
  have h := checkLog_sound (w := (1559 / 20001559)) (n := 12)
    (lo := (155887 / 1000000000)) (hi := (9743 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001559 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001559 / 10000000) = 1/(10000000 / 10001559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_785 : Bounds (155887 / 1000000000) (9743 / 62500000) (Real.log (10001559 / 10000000)) := by
  have h := reflection_log_785_neg
  have he : Real.log (10001559 / 10000000) = -Real.log (10000000 / 10001559) := by
    rw [show ((10001559 / 10000000) : ℝ) = ((10000000 / 10001559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_786_neg : (19489 / 125000000) ≤ -Real.log (9998441 / 10000000) ∧
    -Real.log (9998441 / 10000000) ≤ (155913 / 1000000000) := by
  have h := checkLog_sound (w := (1559 / 19998441)) (n := 12)
    (lo := (19489 / 125000000)) (hi := (155913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998441) = 1/(9998441 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_786 : Bounds (-155913 / 1000000000) (-19489 / 125000000) (Real.log (9998441 / 10000000)) := by
  have h := reflection_log_786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_787_neg : (75260521 / 1000000000) ≤ -Real.log (200000 / 215633) ∧
    -Real.log (200000 / 215633) ≤ (37630261 / 500000000) := by
  have h := checkLog_sound (w := (15633 / 415633)) (n := 12)
    (lo := (75260521 / 1000000000)) (hi := (37630261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215633 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215633 / 200000) = 1/(200000 / 215633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_787 : Bounds (75260521 / 1000000000) (37630261 / 500000000) (Real.log (215633 / 200000)) := by
  have h := reflection_log_787_neg
  have he : Real.log (215633 / 200000) = -Real.log (200000 / 215633) := by
    rw [show ((215633 / 200000) : ℝ) = ((200000 / 215633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_788_neg : (8138903 / 100000000) ≤ -Real.log (184367 / 200000) ∧
    -Real.log (184367 / 200000) ≤ (81389031 / 1000000000) := by
  have h := checkLog_sound (w := (15633 / 384367)) (n := 12)
    (lo := (8138903 / 100000000)) (hi := (81389031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184367) = 1/(184367 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_788 : Bounds (-81389031 / 1000000000) (-8138903 / 100000000) (Real.log (184367 / 200000)) := by
  have h := reflection_log_788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_789_neg : (4715781 / 62500000) ≤ -Real.log (250000 / 269593) ∧
    -Real.log (250000 / 269593) ≤ (75452497 / 1000000000) := by
  have h := checkLog_sound (w := (19593 / 519593)) (n := 12)
    (lo := (4715781 / 62500000)) (hi := (75452497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269593 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269593 / 250000) = 1/(250000 / 269593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_789 : Bounds (4715781 / 62500000) (75452497 / 1000000000) (Real.log (269593 / 250000)) := by
  have h := reflection_log_789_neg
  have he : Real.log (269593 / 250000) = -Real.log (250000 / 269593) := by
    rw [show ((269593 / 250000) : ℝ) = ((250000 / 269593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_790_neg : (81613607 / 1000000000) ≤ -Real.log (230407 / 250000) ∧
    -Real.log (230407 / 250000) ≤ (10201701 / 125000000) := by
  have h := checkLog_sound (w := (19593 / 480407)) (n := 12)
    (lo := (81613607 / 1000000000)) (hi := (10201701 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230407) = 1/(230407 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_790 : Bounds (-10201701 / 125000000) (-81613607 / 1000000000) (Real.log (230407 / 250000)) := by
  have h := reflection_log_790_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_791_neg : (6161111 / 1000000000) ≤ -Real.log (62116114351 / 62500000000) ∧
    -Real.log (62116114351 / 62500000000) ≤ (770139 / 125000000) := by
  have h := checkLog_sound (w := (383885649 / 124616114351)) (n := 12)
    (lo := (6161111 / 1000000000)) (hi := (770139 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62116114351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62116114351) = 1/(62116114351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_791 : Bounds (-770139 / 125000000) (-6161111 / 1000000000) (Real.log (62116114351 / 62500000000)) := by
  have h := reflection_log_791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_792_neg : (1532127 / 250000000) ≤ -Real.log (39755609311 / 40000000000) ∧
    -Real.log (39755609311 / 40000000000) ≤ (6128509 / 1000000000) := by
  have h := checkLog_sound (w := (244390689 / 79755609311)) (n := 12)
    (lo := (1532127 / 250000000)) (hi := (6128509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39755609311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39755609311) = 1/(39755609311 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_792 : Bounds (-6128509 / 1000000000) (-1532127 / 250000000) (Real.log (39755609311 / 40000000000)) := by
  have h := reflection_log_792_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_793_neg : (9790597 / 62500000) ≤ -Real.log (62500000000 / 73099103961) ∧
    -Real.log (62500000000 / 73099103961) ≤ (156649553 / 1000000000) := by
  have h := checkLog_sound (w := (10599103961 / 135599103961)) (n := 12)
    (lo := (9790597 / 62500000)) (hi := (156649553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73099103961 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73099103961 / 62500000000) = 1/(62500000000 / 73099103961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_793 : Bounds (9790597 / 62500000) (156649553 / 1000000000) (Real.log (73099103961 / 62500000000)) := by
  have h := reflection_log_793_neg
  have he : Real.log (73099103961 / 62500000000) = -Real.log (62500000000 / 73099103961) := by
    rw [show ((73099103961 / 62500000000) : ℝ) = ((62500000000 / 73099103961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_794_neg : (19633263 / 125000000) ≤ -Real.log (500000000000 / 585036478927) ∧
    -Real.log (500000000000 / 585036478927) ≤ (31413221 / 200000000) := by
  have h := checkLog_sound (w := (85036478927 / 1085036478927)) (n := 12)
    (lo := (19633263 / 125000000)) (hi := (31413221 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585036478927 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585036478927 / 500000000000) = 1/(500000000000 / 585036478927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_794 : Bounds (19633263 / 125000000) (31413221 / 200000000) (Real.log (585036478927 / 500000000000)) := by
  have h := reflection_log_794_neg
  have he : Real.log (585036478927 / 500000000000) = -Real.log (500000000000 / 585036478927) := by
    rw [show ((585036478927 / 500000000000) : ℝ) = ((500000000000 / 585036478927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_795_neg : (31415859 / 100000000) ≤ -Real.log (500000000000 / 684553423359) ∧
    -Real.log (500000000000 / 684553423359) ≤ (314158591 / 1000000000) := by
  have h := checkLog_sound (w := (184553423359 / 1184553423359)) (n := 12)
    (lo := (31415859 / 100000000)) (hi := (314158591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684553423359 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684553423359 / 500000000000) = 1/(500000000000 / 684553423359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_795 : Bounds (31415859 / 100000000) (314158591 / 1000000000) (Real.log (684553423359 / 500000000000)) := by
  have h := reflection_log_795_neg
  have he : Real.log (684553423359 / 500000000000) = -Real.log (500000000000 / 684553423359) := by
    rw [show ((684553423359 / 500000000000) : ℝ) = ((500000000000 / 684553423359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_796_neg : (314363569 / 1000000000) ≤ -Real.log (62500000000 / 85586719583) ∧
    -Real.log (62500000000 / 85586719583) ≤ (31436357 / 100000000) := by
  have h := checkLog_sound (w := (23086719583 / 148086719583)) (n := 12)
    (lo := (314363569 / 1000000000)) (hi := (31436357 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85586719583 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85586719583 / 62500000000) = 1/(62500000000 / 85586719583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_796 : Bounds (314363569 / 1000000000) (31436357 / 100000000) (Real.log (85586719583 / 62500000000)) := by
  have h := reflection_log_796_neg
  have he : Real.log (85586719583 / 62500000000) = -Real.log (62500000000 / 85586719583) := by
    rw [show ((85586719583 / 62500000000) : ℝ) = ((62500000000 / 85586719583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_797_neg : (14496577 / 100000000) ≤ -Real.log (250 / 289) ∧
    -Real.log (250 / 289) ≤ (144965771 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 539)) (n := 12)
    (lo := (14496577 / 100000000)) (hi := (144965771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(289 / 250) = 1/(250 / 289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_797 : Bounds (14496577 / 100000000) (144965771 / 1000000000) (Real.log (289 / 250)) := by
  have h := reflection_log_797_neg
  have he : Real.log (289 / 250) = -Real.log (250 / 289) := by
    rw [show ((289 / 250) : ℝ) = ((250 / 289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_798_neg : (5300087 / 31250000) ≤ -Real.log (211 / 250) ∧
    -Real.log (211 / 250) ≤ (33920557 / 200000000) := by
  have h := checkLog_sound (w := (39 / 461)) (n := 12)
    (lo := (5300087 / 31250000)) (hi := (33920557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 211) = 1/(211 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_798 : Bounds (-33920557 / 200000000) (-5300087 / 31250000) (Real.log (211 / 250)) := by
  have h := reflection_log_798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_799_neg : (155987 / 1000000000) ≤ -Real.log (250000 / 250039) ∧
    -Real.log (250000 / 250039) ≤ (38997 / 250000000) := by
  have h := checkLog_sound (w := (39 / 500039)) (n := 12)
    (lo := (155987 / 1000000000)) (hi := (38997 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250039 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250039 / 250000) = 1/(250000 / 250039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_799 : Bounds (155987 / 1000000000) (38997 / 250000000) (Real.log (250039 / 250000)) := by
  have h := reflection_log_799_neg
  have he : Real.log (250039 / 250000) = -Real.log (250000 / 250039) := by
    rw [show ((250039 / 250000) : ℝ) = ((250000 / 250039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_800_neg : (39003 / 250000000) ≤ -Real.log (249961 / 250000) ∧
    -Real.log (249961 / 250000) ≤ (156013 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 499961)) (n := 12)
    (lo := (39003 / 250000000)) (hi := (156013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249961) = 1/(249961 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_800 : Bounds (-156013 / 1000000000) (-39003 / 250000000) (Real.log (249961 / 250000)) := by
  have h := reflection_log_800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_801_neg : (75307823 / 1000000000) ≤ -Real.log (125000 / 134777) ∧
    -Real.log (125000 / 134777) ≤ (4706739 / 62500000) := by
  have h := checkLog_sound (w := (9777 / 259777)) (n := 12)
    (lo := (75307823 / 1000000000)) (hi := (4706739 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134777 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134777 / 125000) = 1/(125000 / 134777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_801 : Bounds (75307823 / 1000000000) (4706739 / 62500000) (Real.log (134777 / 125000)) := by
  have h := reflection_log_801_neg
  have he : Real.log (134777 / 125000) = -Real.log (125000 / 134777) := by
    rw [show ((134777 / 125000) : ℝ) = ((125000 / 134777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_802_neg : (20361089 / 250000000) ≤ -Real.log (115223 / 125000) ∧
    -Real.log (115223 / 125000) ≤ (81444357 / 1000000000) := by
  have h := checkLog_sound (w := (9777 / 240223)) (n := 12)
    (lo := (20361089 / 250000000)) (hi := (81444357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115223) = 1/(115223 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_802 : Bounds (-81444357 / 1000000000) (-20361089 / 250000000) (Real.log (115223 / 125000)) := by
  have h := reflection_log_802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_803_neg : (18874947 / 250000000) ≤ -Real.log (1000000 / 1078423) ∧
    -Real.log (1000000 / 1078423) ≤ (75499789 / 1000000000) := by
  have h := checkLog_sound (w := (78423 / 2078423)) (n := 12)
    (lo := (18874947 / 250000000)) (hi := (75499789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078423 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078423 / 1000000) = 1/(1000000 / 1078423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_803 : Bounds (18874947 / 250000000) (75499789 / 1000000000) (Real.log (1078423 / 1000000)) := by
  have h := reflection_log_803_neg
  have he : Real.log (1078423 / 1000000) = -Real.log (1000000 / 1078423) := by
    rw [show ((1078423 / 1000000) : ℝ) = ((1000000 / 1078423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_804_neg : (16333789 / 200000000) ≤ -Real.log (921577 / 1000000) ∧
    -Real.log (921577 / 1000000) ≤ (40834473 / 500000000) := by
  have h := checkLog_sound (w := (78423 / 1921577)) (n := 12)
    (lo := (16333789 / 200000000)) (hi := (40834473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921577) = 1/(921577 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_804 : Bounds (-40834473 / 500000000) (-16333789 / 200000000) (Real.log (921577 / 1000000)) := by
  have h := reflection_log_804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_805_neg : (6169157 / 1000000000) ≤ -Real.log (993849833071 / 1000000000000) ∧
    -Real.log (993849833071 / 1000000000000) ≤ (3084579 / 500000000) := by
  have h := checkLog_sound (w := (6150166929 / 1993849833071)) (n := 12)
    (lo := (6169157 / 1000000000)) (hi := (3084579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993849833071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993849833071) = 1/(993849833071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_805 : Bounds (-3084579 / 500000000) (-6169157 / 1000000000) (Real.log (993849833071 / 1000000000000)) := by
  have h := reflection_log_805_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_806_neg : (1534133 / 250000000) ≤ -Real.log (15529410271 / 15625000000) ∧
    -Real.log (15529410271 / 15625000000) ≤ (6136533 / 1000000000) := by
  have h := checkLog_sound (w := (95589729 / 31154410271)) (n := 12)
    (lo := (1534133 / 250000000)) (hi := (6136533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15529410271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15529410271) = 1/(15529410271 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_806 : Bounds (-6136533 / 1000000000) (-1534133 / 250000000) (Real.log (15529410271 / 15625000000)) := by
  have h := reflection_log_806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_807_neg : (156752179 / 1000000000) ≤ -Real.log (500000000000 / 584852850559) ∧
    -Real.log (500000000000 / 584852850559) ≤ (7837609 / 50000000) := by
  have h := checkLog_sound (w := (84852850559 / 1084852850559)) (n := 12)
    (lo := (156752179 / 1000000000)) (hi := (7837609 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584852850559 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584852850559 / 500000000000) = 1/(500000000000 / 584852850559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_807 : Bounds (156752179 / 1000000000) (7837609 / 50000000) (Real.log (584852850559 / 500000000000)) := by
  have h := reflection_log_807_neg
  have he : Real.log (584852850559 / 500000000000) = -Real.log (500000000000 / 584852850559) := by
    rw [show ((584852850559 / 500000000000) : ℝ) = ((500000000000 / 584852850559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_808_neg : (78584367 / 500000000) ≤ -Real.log (250000000000 / 292548262381) ∧
    -Real.log (250000000000 / 292548262381) ≤ (31433747 / 200000000) := by
  have h := checkLog_sound (w := (42548262381 / 542548262381)) (n := 12)
    (lo := (78584367 / 500000000)) (hi := (31433747 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292548262381 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292548262381 / 250000000000) = 1/(250000000000 / 292548262381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_808 : Bounds (78584367 / 500000000) (31433747 / 200000000) (Real.log (292548262381 / 250000000000)) := by
  have h := reflection_log_808_neg
  have he : Real.log (292548262381 / 250000000000) = -Real.log (250000000000 / 292548262381) := by
    rw [show ((292548262381 / 250000000000) : ℝ) = ((250000000000 / 292548262381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_809_neg : (314363569 / 1000000000) ≤ -Real.log (500000000000 / 684693756663) ∧
    -Real.log (500000000000 / 684693756663) ≤ (31436357 / 100000000) := by
  have h := checkLog_sound (w := (184693756663 / 1184693756663)) (n := 12)
    (lo := (314363569 / 1000000000)) (hi := (31436357 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684693756663 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684693756663 / 500000000000) = 1/(500000000000 / 684693756663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_809 : Bounds (314363569 / 1000000000) (31436357 / 100000000) (Real.log (684693756663 / 500000000000)) := by
  have h := reflection_log_809_neg
  have he : Real.log (684693756663 / 500000000000) = -Real.log (500000000000 / 684693756663) := by
    rw [show ((684693756663 / 500000000000) : ℝ) = ((500000000000 / 684693756663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_810_neg : (157284277 / 500000000) ≤ -Real.log (500000000000 / 684834123223) ∧
    -Real.log (500000000000 / 684834123223) ≤ (62913711 / 200000000) := by
  have h := checkLog_sound (w := (184834123223 / 1184834123223)) (n := 12)
    (lo := (157284277 / 500000000)) (hi := (62913711 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684834123223 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684834123223 / 500000000000) = 1/(500000000000 / 684834123223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_810 : Bounds (157284277 / 500000000) (62913711 / 200000000) (Real.log (684834123223 / 500000000000)) := by
  have h := reflection_log_810_neg
  have he : Real.log (684834123223 / 500000000000) = -Real.log (500000000000 / 684834123223) := by
    rw [show ((684834123223 / 500000000000) : ℝ) = ((500000000000 / 684834123223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_811_neg : (145052271 / 1000000000) ≤ -Real.log (10000 / 11561) ∧
    -Real.log (10000 / 11561) ≤ (9065767 / 62500000) := by
  have h := checkLog_sound (w := (1561 / 21561)) (n := 12)
    (lo := (145052271 / 1000000000)) (hi := (9065767 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11561 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11561 / 10000) = 1/(10000 / 11561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_811 : Bounds (145052271 / 1000000000) (9065767 / 62500000) (Real.log (11561 / 10000)) := by
  have h := reflection_log_811_neg
  have he : Real.log (11561 / 10000) = -Real.log (10000 / 11561) := by
    rw [show ((11561 / 10000) : ℝ) = ((10000 / 11561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_812_neg : (84860637 / 500000000) ≤ -Real.log (8439 / 10000) ∧
    -Real.log (8439 / 10000) ≤ (6788851 / 40000000) := by
  have h := checkLog_sound (w := (1561 / 18439)) (n := 12)
    (lo := (84860637 / 500000000)) (hi := (6788851 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8439) = 1/(8439 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_812 : Bounds (-6788851 / 40000000) (-84860637 / 500000000) (Real.log (8439 / 10000)) := by
  have h := reflection_log_812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_813_neg : (156087 / 1000000000) ≤ -Real.log (10000000 / 10001561) ∧
    -Real.log (10000000 / 10001561) ≤ (19511 / 125000000) := by
  have h := checkLog_sound (w := (1561 / 20001561)) (n := 12)
    (lo := (156087 / 1000000000)) (hi := (19511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001561 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001561 / 10000000) = 1/(10000000 / 10001561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_813 : Bounds (156087 / 1000000000) (19511 / 125000000) (Real.log (10001561 / 10000000)) := by
  have h := reflection_log_813_neg
  have he : Real.log (10001561 / 10000000) = -Real.log (10000000 / 10001561) := by
    rw [show ((10001561 / 10000000) : ℝ) = ((10000000 / 10001561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_814_neg : (9757 / 62500000) ≤ -Real.log (9998439 / 10000000) ∧
    -Real.log (9998439 / 10000000) ≤ (156113 / 1000000000) := by
  have h := checkLog_sound (w := (1561 / 19998439)) (n := 12)
    (lo := (9757 / 62500000)) (hi := (156113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998439) = 1/(9998439 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_814 : Bounds (-156113 / 1000000000) (-9757 / 62500000) (Real.log (9998439 / 10000000)) := by
  have h := reflection_log_814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_815_neg : (37677561 / 500000000) ≤ -Real.log (1000000 / 1078267) ∧
    -Real.log (1000000 / 1078267) ≤ (75355123 / 1000000000) := by
  have h := checkLog_sound (w := (78267 / 2078267)) (n := 12)
    (lo := (37677561 / 500000000)) (hi := (75355123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078267 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078267 / 1000000) = 1/(1000000 / 1078267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_815 : Bounds (37677561 / 500000000) (75355123 / 1000000000) (Real.log (1078267 / 1000000)) := by
  have h := reflection_log_815_neg
  have he : Real.log (1078267 / 1000000) = -Real.log (1000000 / 1078267) := by
    rw [show ((1078267 / 1000000) : ℝ) = ((1000000 / 1078267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_816_neg : (16299937 / 200000000) ≤ -Real.log (921733 / 1000000) ∧
    -Real.log (921733 / 1000000) ≤ (40749843 / 500000000) := by
  have h := checkLog_sound (w := (78267 / 1921733)) (n := 12)
    (lo := (16299937 / 200000000)) (hi := (40749843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921733) = 1/(921733 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_816 : Bounds (-40749843 / 500000000) (-16299937 / 200000000) (Real.log (921733 / 1000000)) := by
  have h := reflection_log_816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_817_neg : (37773539 / 500000000) ≤ -Real.log (500000 / 539237) ∧
    -Real.log (500000 / 539237) ≤ (75547079 / 1000000000) := by
  have h := checkLog_sound (w := (39237 / 1039237)) (n := 12)
    (lo := (37773539 / 500000000)) (hi := (75547079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539237 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539237 / 500000) = 1/(500000 / 539237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_817 : Bounds (37773539 / 500000000) (75547079 / 1000000000) (Real.log (539237 / 500000)) := by
  have h := reflection_log_817_neg
  have he : Real.log (539237 / 500000) = -Real.log (500000 / 539237) := by
    rw [show ((539237 / 500000) : ℝ) = ((500000 / 539237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_818_neg : (81724287 / 1000000000) ≤ -Real.log (460763 / 500000) ∧
    -Real.log (460763 / 500000) ≤ (638471 / 7812500) := by
  have h := checkLog_sound (w := (39237 / 960763)) (n := 12)
    (lo := (81724287 / 1000000000)) (hi := (638471 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460763) = 1/(460763 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_818 : Bounds (-638471 / 7812500) (-81724287 / 1000000000) (Real.log (460763 / 500000)) := by
  have h := reflection_log_818_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_819_neg : (772151 / 125000000) ≤ -Real.log (248460457831 / 250000000000) ∧
    -Real.log (248460457831 / 250000000000) ≤ (6177209 / 1000000000) := by
  have h := checkLog_sound (w := (1539542169 / 498460457831)) (n := 12)
    (lo := (772151 / 125000000)) (hi := (6177209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248460457831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248460457831) = 1/(248460457831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_819 : Bounds (-6177209 / 1000000000) (-772151 / 125000000) (Real.log (248460457831 / 250000000000)) := by
  have h := reflection_log_819_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_820_neg : (3072281 / 500000000) ≤ -Real.log (993874276711 / 1000000000000) ∧
    -Real.log (993874276711 / 1000000000000) ≤ (6144563 / 1000000000) := by
  have h := checkLog_sound (w := (6125723289 / 1993874276711)) (n := 12)
    (lo := (3072281 / 500000000)) (hi := (6144563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993874276711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993874276711) = 1/(993874276711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_820 : Bounds (-6144563 / 1000000000) (-3072281 / 500000000) (Real.log (993874276711 / 1000000000000)) := by
  have h := reflection_log_820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_821_neg : (156854807 / 1000000000) ≤ -Real.log (500000000000 / 584912876071) ∧
    -Real.log (500000000000 / 584912876071) ≤ (19606851 / 125000000) := by
  have h := checkLog_sound (w := (84912876071 / 1084912876071)) (n := 12)
    (lo := (156854807 / 1000000000)) (hi := (19606851 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584912876071 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584912876071 / 500000000000) = 1/(500000000000 / 584912876071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_821 : Bounds (156854807 / 1000000000) (19606851 / 125000000) (Real.log (584912876071 / 500000000000)) := by
  have h := reflection_log_821_neg
  have he : Real.log (584912876071 / 500000000000) = -Real.log (500000000000 / 584912876071) := by
    rw [show ((584912876071 / 500000000000) : ℝ) = ((500000000000 / 584912876071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_822_neg : (78635683 / 500000000) ≤ -Real.log (500000000000 / 585156577243) ∧
    -Real.log (500000000000 / 585156577243) ≤ (157271367 / 1000000000) := by
  have h := checkLog_sound (w := (85156577243 / 1085156577243)) (n := 12)
    (lo := (78635683 / 500000000)) (hi := (157271367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585156577243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585156577243 / 500000000000) = 1/(500000000000 / 585156577243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_822 : Bounds (78635683 / 500000000) (157271367 / 1000000000) (Real.log (585156577243 / 500000000000)) := by
  have h := reflection_log_822_neg
  have he : Real.log (585156577243 / 500000000000) = -Real.log (500000000000 / 585156577243) := by
    rw [show ((585156577243 / 500000000000) : ℝ) = ((500000000000 / 585156577243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_823_neg : (157284277 / 500000000) ≤ -Real.log (250000000000 / 342417061611) ∧
    -Real.log (250000000000 / 342417061611) ≤ (62913711 / 200000000) := by
  have h := checkLog_sound (w := (92417061611 / 592417061611)) (n := 12)
    (lo := (157284277 / 500000000)) (hi := (62913711 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342417061611 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342417061611 / 250000000000) = 1/(250000000000 / 342417061611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_823 : Bounds (157284277 / 500000000) (62913711 / 200000000) (Real.log (342417061611 / 250000000000)) := by
  have h := reflection_log_823_neg
  have he : Real.log (342417061611 / 250000000000) = -Real.log (250000000000 / 342417061611) := by
    rw [show ((342417061611 / 250000000000) : ℝ) = ((250000000000 / 342417061611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_824_neg : (157386773 / 500000000) ≤ -Real.log (62500000000 / 85621815381) ∧
    -Real.log (62500000000 / 85621815381) ≤ (314773547 / 1000000000) := by
  have h := checkLog_sound (w := (23121815381 / 148121815381)) (n := 12)
    (lo := (157386773 / 500000000)) (hi := (314773547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85621815381 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85621815381 / 62500000000) = 1/(62500000000 / 85621815381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_824 : Bounds (157386773 / 500000000) (314773547 / 1000000000) (Real.log (85621815381 / 62500000000)) := by
  have h := reflection_log_824_neg
  have he : Real.log (85621815381 / 62500000000) = -Real.log (62500000000 / 85621815381) := by
    rw [show ((85621815381 / 62500000000) : ℝ) = ((62500000000 / 85621815381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_825_neg : (29027753 / 200000000) ≤ -Real.log (5000 / 5781) ∧
    -Real.log (5000 / 5781) ≤ (72569383 / 500000000) := by
  have h := checkLog_sound (w := (781 / 10781)) (n := 12)
    (lo := (29027753 / 200000000)) (hi := (72569383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5781 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5781 / 5000) = 1/(5000 / 5781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_825 : Bounds (29027753 / 200000000) (72569383 / 500000000) (Real.log (5781 / 5000)) := by
  have h := reflection_log_825_neg
  have he : Real.log (5781 / 5000) = -Real.log (5000 / 5781) := by
    rw [show ((5781 / 5000) : ℝ) = ((5000 / 5781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_826_neg : (169839779 / 1000000000) ≤ -Real.log (4219 / 5000) ∧
    -Real.log (4219 / 5000) ≤ (8491989 / 50000000) := by
  have h := checkLog_sound (w := (781 / 9219)) (n := 12)
    (lo := (169839779 / 1000000000)) (hi := (8491989 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4219) = 1/(4219 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_826 : Bounds (-8491989 / 50000000) (-169839779 / 1000000000) (Real.log (4219 / 5000)) := by
  have h := reflection_log_826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_827_neg : (156187 / 1000000000) ≤ -Real.log (5000000 / 5000781) ∧
    -Real.log (5000000 / 5000781) ≤ (39047 / 250000000) := by
  have h := checkLog_sound (w := (781 / 10000781)) (n := 12)
    (lo := (156187 / 1000000000)) (hi := (39047 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000781 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000781 / 5000000) = 1/(5000000 / 5000781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_827 : Bounds (156187 / 1000000000) (39047 / 250000000) (Real.log (5000781 / 5000000)) := by
  have h := reflection_log_827_neg
  have he : Real.log (5000781 / 5000000) = -Real.log (5000000 / 5000781) := by
    rw [show ((5000781 / 5000000) : ℝ) = ((5000000 / 5000781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_828_neg : (39053 / 250000000) ≤ -Real.log (4999219 / 5000000) ∧
    -Real.log (4999219 / 5000000) ≤ (156213 / 1000000000) := by
  have h := checkLog_sound (w := (781 / 9999219)) (n := 12)
    (lo := (39053 / 250000000)) (hi := (156213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999219) = 1/(4999219 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_828 : Bounds (-156213 / 1000000000) (-39053 / 250000000) (Real.log (4999219 / 5000000)) := by
  have h := reflection_log_828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_829_neg : (18850373 / 250000000) ≤ -Real.log (1000000 / 1078317) ∧
    -Real.log (1000000 / 1078317) ≤ (75401493 / 1000000000) := by
  have h := checkLog_sound (w := (78317 / 2078317)) (n := 12)
    (lo := (18850373 / 250000000)) (hi := (75401493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078317 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078317 / 1000000) = 1/(1000000 / 1078317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_829 : Bounds (18850373 / 250000000) (75401493 / 1000000000) (Real.log (1078317 / 1000000)) := by
  have h := reflection_log_829_neg
  have he : Real.log (1078317 / 1000000) = -Real.log (1000000 / 1078317) := by
    rw [show ((1078317 / 1000000) : ℝ) = ((1000000 / 1078317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_830_neg : (20388483 / 250000000) ≤ -Real.log (921683 / 1000000) ∧
    -Real.log (921683 / 1000000) ≤ (81553933 / 1000000000) := by
  have h := checkLog_sound (w := (78317 / 1921683)) (n := 12)
    (lo := (20388483 / 250000000)) (hi := (81553933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921683) = 1/(921683 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_830 : Bounds (-81553933 / 1000000000) (-20388483 / 250000000) (Real.log (921683 / 1000000)) := by
  have h := reflection_log_830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_831_neg : (75593439 / 1000000000) ≤ -Real.log (250000 / 269631) ∧
    -Real.log (250000 / 269631) ≤ (472459 / 6250000) := by
  have h := checkLog_sound (w := (19631 / 519631)) (n := 12)
    (lo := (75593439 / 1000000000)) (hi := (472459 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269631 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269631 / 250000) = 1/(250000 / 269631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_831 : Bounds (75593439 / 1000000000) (472459 / 6250000) (Real.log (269631 / 250000)) := by
  have h := reflection_log_831_neg
  have he : Real.log (269631 / 250000) = -Real.log (250000 / 269631) := by
    rw [show ((269631 / 250000) : ℝ) = ((250000 / 269631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
