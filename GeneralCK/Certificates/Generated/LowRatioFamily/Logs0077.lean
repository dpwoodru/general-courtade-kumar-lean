import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4928_neg : (92741 / 500000000) ≤ -Real.log (2000000 / 2000371) ∧
    -Real.log (2000000 / 2000371) ≤ (185483 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 4000371)) (n := 12)
    (lo := (92741 / 500000000)) (hi := (185483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000371 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000371 / 2000000) = 1/(2000000 / 2000371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4928 : Bounds (92741 / 500000000) (185483 / 1000000000) (Real.log (2000371 / 2000000)) := by
  have h := reflection_log_4928_neg
  have he : Real.log (2000371 / 2000000) = -Real.log (2000000 / 2000371) := by
    rw [show ((2000371 / 2000000) : ℝ) = ((2000000 / 2000371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4929_neg : (185517 / 1000000000) ≤ -Real.log (1999629 / 2000000) ∧
    -Real.log (1999629 / 2000000) ≤ (92759 / 500000000) := by
  have h := checkLog_sound (w := (371 / 3999629)) (n := 12)
    (lo := (185517 / 1000000000)) (hi := (92759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999629) = 1/(1999629 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4929 : Bounds (-92759 / 500000000) (-185517 / 1000000000) (Real.log (1999629 / 2000000)) := by
  have h := reflection_log_4929_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4930_neg : (44549099 / 500000000) ≤ -Real.log (250000 / 273297) ∧
    -Real.log (250000 / 273297) ≤ (89098199 / 1000000000) := by
  have h := checkLog_sound (w := (23297 / 523297)) (n := 12)
    (lo := (44549099 / 500000000)) (hi := (89098199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273297 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273297 / 250000) = 1/(250000 / 273297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4930 : Bounds (44549099 / 500000000) (89098199 / 1000000000) (Real.log (273297 / 250000)) := by
  have h := reflection_log_4930_neg
  have he : Real.log (273297 / 250000) = -Real.log (250000 / 273297) := by
    rw [show ((273297 / 250000) : ℝ) = ((250000 / 273297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4931_neg : (97820127 / 1000000000) ≤ -Real.log (226703 / 250000) ∧
    -Real.log (226703 / 250000) ≤ (3056879 / 31250000) := by
  have h := checkLog_sound (w := (23297 / 476703)) (n := 12)
    (lo := (97820127 / 1000000000)) (hi := (3056879 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226703) = 1/(226703 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4931 : Bounds (-3056879 / 31250000) (-97820127 / 1000000000) (Real.log (226703 / 250000)) := by
  have h := reflection_log_4931_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4932_neg : (89314057 / 1000000000) ≤ -Real.log (62500 / 68339) ∧
    -Real.log (62500 / 68339) ≤ (44657029 / 500000000) := by
  have h := checkLog_sound (w := (5839 / 130839)) (n := 12)
    (lo := (89314057 / 1000000000)) (hi := (44657029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68339 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68339 / 62500) = 1/(62500 / 68339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4932 : Bounds (89314057 / 1000000000) (44657029 / 500000000) (Real.log (68339 / 62500)) := by
  have h := reflection_log_4932_neg
  have he : Real.log (68339 / 62500) = -Real.log (62500 / 68339) := by
    rw [show ((68339 / 62500) : ℝ) = ((62500 / 68339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4933_neg : (98080413 / 1000000000) ≤ -Real.log (56661 / 62500) ∧
    -Real.log (56661 / 62500) ≤ (49040207 / 500000000) := by
  have h := checkLog_sound (w := (5839 / 119161)) (n := 12)
    (lo := (98080413 / 1000000000)) (hi := (49040207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56661) = 1/(56661 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4933 : Bounds (-49040207 / 500000000) (-98080413 / 1000000000) (Real.log (56661 / 62500)) := by
  have h := reflection_log_4933_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4934_neg : (2191589 / 250000000) ≤ -Real.log (3872156079 / 3906250000) ∧
    -Real.log (3872156079 / 3906250000) ≤ (8766357 / 1000000000) := by
  have h := checkLog_sound (w := (34093921 / 7778406079)) (n := 12)
    (lo := (2191589 / 250000000)) (hi := (8766357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3872156079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3872156079) = 1/(3872156079 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4934 : Bounds (-8766357 / 1000000000) (-2191589 / 250000000) (Real.log (3872156079 / 3906250000)) := by
  have h := reflection_log_4934_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4935_neg : (8721929 / 1000000000) ≤ -Real.log (61957249791 / 62500000000) ∧
    -Real.log (61957249791 / 62500000000) ≤ (872193 / 100000000) := by
  have h := checkLog_sound (w := (542750209 / 124457249791)) (n := 12)
    (lo := (8721929 / 1000000000)) (hi := (872193 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61957249791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61957249791) = 1/(61957249791 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4935 : Bounds (-872193 / 100000000) (-8721929 / 1000000000) (Real.log (61957249791 / 62500000000)) := by
  have h := reflection_log_4935_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4936_neg : (7476733 / 40000000) ≤ -Real.log (250000000000 / 301382204911) ∧
    -Real.log (250000000000 / 301382204911) ≤ (93459163 / 500000000) := by
  have h := checkLog_sound (w := (51382204911 / 551382204911)) (n := 12)
    (lo := (7476733 / 40000000)) (hi := (93459163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301382204911 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301382204911 / 250000000000) = 1/(250000000000 / 301382204911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4936 : Bounds (7476733 / 40000000) (93459163 / 500000000) (Real.log (301382204911 / 250000000000)) := by
  have h := reflection_log_4936_neg
  have he : Real.log (301382204911 / 250000000000) = -Real.log (250000000000 / 301382204911) := by
    rw [show ((301382204911 / 250000000000) : ℝ) = ((250000000000 / 301382204911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4937_neg : (18739447 / 100000000) ≤ -Real.log (500000000000 / 603051481619) ∧
    -Real.log (500000000000 / 603051481619) ≤ (187394471 / 1000000000) := by
  have h := checkLog_sound (w := (103051481619 / 1103051481619)) (n := 12)
    (lo := (18739447 / 100000000)) (hi := (187394471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603051481619 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603051481619 / 500000000000) = 1/(500000000000 / 603051481619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4937 : Bounds (18739447 / 100000000) (187394471 / 1000000000) (Real.log (603051481619 / 500000000000)) := by
  have h := reflection_log_4937_neg
  have he : Real.log (603051481619 / 500000000000) = -Real.log (500000000000 / 603051481619) := by
    rw [show ((603051481619 / 500000000000) : ℝ) = ((500000000000 / 603051481619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4938_neg : (187569177 / 500000000) ≤ -Real.log (250000000000 / 363798183157) ∧
    -Real.log (250000000000 / 363798183157) ≤ (75027671 / 200000000) := by
  have h := checkLog_sound (w := (113798183157 / 613798183157)) (n := 12)
    (lo := (187569177 / 500000000)) (hi := (75027671 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363798183157 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363798183157 / 250000000000) = 1/(250000000000 / 363798183157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4938 : Bounds (187569177 / 500000000) (75027671 / 200000000) (Real.log (363798183157 / 250000000000)) := by
  have h := reflection_log_4938_neg
  have he : Real.log (363798183157 / 250000000000) = -Real.log (250000000000 / 363798183157) := by
    rw [show ((363798183157 / 250000000000) : ℝ) = ((250000000000 / 363798183157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4939_neg : (375345477 / 1000000000) ≤ -Real.log (500000000000 / 727747084101) ∧
    -Real.log (500000000000 / 727747084101) ≤ (187672739 / 500000000) := by
  have h := checkLog_sound (w := (227747084101 / 1227747084101)) (n := 12)
    (lo := (375345477 / 1000000000)) (hi := (187672739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727747084101 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727747084101 / 500000000000) = 1/(500000000000 / 727747084101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4939 : Bounds (375345477 / 1000000000) (187672739 / 500000000) (Real.log (727747084101 / 500000000000)) := by
  have h := reflection_log_4939_neg
  have he : Real.log (727747084101 / 500000000000) = -Real.log (500000000000 / 727747084101) := by
    rw [show ((727747084101 / 500000000000) : ℝ) = ((500000000000 / 727747084101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4940_neg : (6809959 / 40000000) ≤ -Real.log (625 / 741) ∧
    -Real.log (625 / 741) ≤ (10640561 / 62500000) := by
  have h := checkLog_sound (w := (58 / 683)) (n := 12)
    (lo := (6809959 / 40000000)) (hi := (10640561 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741 / 625) = 1/(625 / 741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4940 : Bounds (6809959 / 40000000) (10640561 / 62500000) (Real.log (741 / 625)) := by
  have h := reflection_log_4940_neg
  have he : Real.log (741 / 625) = -Real.log (625 / 741) := by
    rw [show ((741 / 625) : ℝ) = ((625 / 741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4941_neg : (205303633 / 1000000000) ≤ -Real.log (509 / 625) ∧
    -Real.log (509 / 625) ≤ (102651817 / 500000000) := by
  have h := checkLog_sound (w := (58 / 567)) (n := 12)
    (lo := (205303633 / 1000000000)) (hi := (102651817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 509) = 1/(509 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4941 : Bounds (-102651817 / 500000000) (-205303633 / 1000000000) (Real.log (509 / 625)) := by
  have h := reflection_log_4941_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4942_neg : (92791 / 500000000) ≤ -Real.log (156250 / 156279) ∧
    -Real.log (156250 / 156279) ≤ (185583 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 312529)) (n := 12)
    (lo := (92791 / 500000000)) (hi := (185583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156279 / 156250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156279 / 156250) = 1/(156250 / 156279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4942 : Bounds (92791 / 500000000) (185583 / 1000000000) (Real.log (156279 / 156250)) := by
  have h := reflection_log_4942_neg
  have he : Real.log (156279 / 156250) = -Real.log (156250 / 156279) := by
    rw [show ((156279 / 156250) : ℝ) = ((156250 / 156279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4943_neg : (185617 / 1000000000) ≤ -Real.log (156221 / 156250) ∧
    -Real.log (156221 / 156250) ≤ (92809 / 500000000) := by
  have h := checkLog_sound (w := (29 / 312471)) (n := 12)
    (lo := (185617 / 1000000000)) (hi := (92809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250 / 156221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250 / 156221) = 1/(156221 / 156250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4943 : Bounds (-92809 / 500000000) (-185617 / 1000000000) (Real.log (156221 / 156250)) := by
  have h := reflection_log_4943_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4944_neg : (89144849 / 1000000000) ≤ -Real.log (1000000 / 1093239) ∧
    -Real.log (1000000 / 1093239) ≤ (1782897 / 20000000) := by
  have h := checkLog_sound (w := (93239 / 2093239)) (n := 12)
    (lo := (89144849 / 1000000000)) (hi := (1782897 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093239 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093239 / 1000000) = 1/(1000000 / 1093239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4944 : Bounds (89144849 / 1000000000) (1782897 / 20000000) (Real.log (1093239 / 1000000)) := by
  have h := reflection_log_4944_neg
  have he : Real.log (1093239 / 1000000) = -Real.log (1000000 / 1093239) := by
    rw [show ((1093239 / 1000000) : ℝ) = ((1000000 / 1093239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4945_neg : (97876369 / 1000000000) ≤ -Real.log (906761 / 1000000) ∧
    -Real.log (906761 / 1000000) ≤ (9787637 / 100000000) := by
  have h := checkLog_sound (w := (93239 / 1906761)) (n := 12)
    (lo := (97876369 / 1000000000)) (hi := (9787637 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906761) = 1/(906761 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4945 : Bounds (-9787637 / 100000000) (-97876369 / 1000000000) (Real.log (906761 / 1000000)) := by
  have h := reflection_log_4945_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4946_neg : (44680349 / 500000000) ≤ -Real.log (40000 / 43739) ∧
    -Real.log (40000 / 43739) ≤ (89360699 / 1000000000) := by
  have h := checkLog_sound (w := (3739 / 83739)) (n := 12)
    (lo := (44680349 / 500000000)) (hi := (89360699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43739 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43739 / 40000) = 1/(40000 / 43739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4946 : Bounds (44680349 / 500000000) (89360699 / 1000000000) (Real.log (43739 / 40000)) := by
  have h := reflection_log_4946_neg
  have he : Real.log (43739 / 40000) = -Real.log (40000 / 43739) := by
    rw [show ((43739 / 40000) : ℝ) = ((40000 / 43739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4947_neg : (9813667 / 100000000) ≤ -Real.log (36261 / 40000) ∧
    -Real.log (36261 / 40000) ≤ (98136671 / 1000000000) := by
  have h := checkLog_sound (w := (3739 / 76261)) (n := 12)
    (lo := (9813667 / 100000000)) (hi := (98136671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36261) = 1/(36261 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4947 : Bounds (-98136671 / 1000000000) (-9813667 / 100000000) (Real.log (36261 / 40000)) := by
  have h := reflection_log_4947_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4948_neg : (2193993 / 250000000) ≤ -Real.log (1586019879 / 1600000000) ∧
    -Real.log (1586019879 / 1600000000) ≤ (8775973 / 1000000000) := by
  have h := checkLog_sound (w := (13980121 / 3186019879)) (n := 12)
    (lo := (2193993 / 250000000)) (hi := (8775973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1586019879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1586019879) = 1/(1586019879 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4948 : Bounds (-8775973 / 1000000000) (-2193993 / 250000000) (Real.log (1586019879 / 1600000000)) := by
  have h := reflection_log_4948_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4949_neg : (13643 / 1562500) ≤ -Real.log (991306488879 / 1000000000000) ∧
    -Real.log (991306488879 / 1000000000000) ≤ (8731521 / 1000000000) := by
  have h := checkLog_sound (w := (8693511121 / 1991306488879)) (n := 12)
    (lo := (13643 / 1562500)) (hi := (8731521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991306488879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991306488879) = 1/(991306488879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4949 : Bounds (-8731521 / 1000000000) (-13643 / 1562500) (Real.log (991306488879 / 1000000000000)) := by
  have h := reflection_log_4949_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4950_neg : (187021219 / 1000000000) ≤ -Real.log (500000000000 / 602826433867) ∧
    -Real.log (500000000000 / 602826433867) ≤ (9351061 / 50000000) := by
  have h := checkLog_sound (w := (102826433867 / 1102826433867)) (n := 12)
    (lo := (187021219 / 1000000000)) (hi := (9351061 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602826433867 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602826433867 / 500000000000) = 1/(500000000000 / 602826433867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4950 : Bounds (187021219 / 1000000000) (9351061 / 50000000) (Real.log (602826433867 / 500000000000)) := by
  have h := reflection_log_4950_neg
  have he : Real.log (602826433867 / 500000000000) = -Real.log (500000000000 / 602826433867) := by
    rw [show ((602826433867 / 500000000000) : ℝ) = ((500000000000 / 602826433867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4951_neg : (187497369 / 1000000000) ≤ -Real.log (500000000000 / 603113537961) ∧
    -Real.log (500000000000 / 603113537961) ≤ (18749737 / 100000000) := by
  have h := checkLog_sound (w := (103113537961 / 1103113537961)) (n := 12)
    (lo := (187497369 / 1000000000)) (hi := (18749737 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603113537961 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603113537961 / 500000000000) = 1/(500000000000 / 603113537961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4951 : Bounds (187497369 / 1000000000) (18749737 / 100000000) (Real.log (603113537961 / 500000000000)) := by
  have h := reflection_log_4951_neg
  have he : Real.log (603113537961 / 500000000000) = -Real.log (500000000000 / 603113537961) := by
    rw [show ((603113537961 / 500000000000) : ℝ) = ((500000000000 / 603113537961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4952_neg : (375345477 / 1000000000) ≤ -Real.log (5000000000 / 7277470841) ∧
    -Real.log (5000000000 / 7277470841) ≤ (187672739 / 500000000) := by
  have h := checkLog_sound (w := (2277470841 / 12277470841)) (n := 12)
    (lo := (375345477 / 1000000000)) (hi := (187672739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7277470841 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7277470841 / 5000000000) = 1/(5000000000 / 7277470841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4952 : Bounds (375345477 / 1000000000) (187672739 / 500000000) (Real.log (7277470841 / 5000000000)) := by
  have h := reflection_log_4952_neg
  have he : Real.log (7277470841 / 5000000000) = -Real.log (5000000000 / 7277470841) := by
    rw [show ((7277470841 / 5000000000) : ℝ) = ((5000000000 / 7277470841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4953_neg : (11736019 / 31250000) ≤ -Real.log (5000000000 / 7278978389) ∧
    -Real.log (5000000000 / 7278978389) ≤ (375552609 / 1000000000) := by
  have h := checkLog_sound (w := (2278978389 / 12278978389)) (n := 12)
    (lo := (11736019 / 31250000)) (hi := (375552609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7278978389 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7278978389 / 5000000000) = 1/(5000000000 / 7278978389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4953 : Bounds (11736019 / 31250000) (375552609 / 1000000000) (Real.log (7278978389 / 5000000000)) := by
  have h := reflection_log_4953_neg
  have he : Real.log (7278978389 / 5000000000) = -Real.log (5000000000 / 7278978389) := by
    rw [show ((7278978389 / 5000000000) : ℝ) = ((5000000000 / 7278978389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4954_neg : (170333317 / 1000000000) ≤ -Real.log (10000 / 11857) ∧
    -Real.log (10000 / 11857) ≤ (85166659 / 500000000) := by
  have h := checkLog_sound (w := (1857 / 21857)) (n := 12)
    (lo := (170333317 / 1000000000)) (hi := (85166659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11857 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11857 / 10000) = 1/(10000 / 11857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4954 : Bounds (170333317 / 1000000000) (85166659 / 500000000) (Real.log (11857 / 10000)) := by
  have h := reflection_log_4954_neg
  have he : Real.log (11857 / 10000) = -Real.log (10000 / 11857) := by
    rw [show ((11857 / 10000) : ℝ) = ((10000 / 11857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4955_neg : (20542643 / 100000000) ≤ -Real.log (8143 / 10000) ∧
    -Real.log (8143 / 10000) ≤ (205426431 / 1000000000) := by
  have h := checkLog_sound (w := (1857 / 18143)) (n := 12)
    (lo := (20542643 / 100000000)) (hi := (205426431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8143) = 1/(8143 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4955 : Bounds (-205426431 / 1000000000) (-20542643 / 100000000) (Real.log (8143 / 10000)) := by
  have h := reflection_log_4955_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4956_neg : (92841 / 500000000) ≤ -Real.log (10000000 / 10001857) ∧
    -Real.log (10000000 / 10001857) ≤ (185683 / 1000000000) := by
  have h := checkLog_sound (w := (1857 / 20001857)) (n := 12)
    (lo := (92841 / 500000000)) (hi := (185683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001857 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001857 / 10000000) = 1/(10000000 / 10001857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4956 : Bounds (92841 / 500000000) (185683 / 1000000000) (Real.log (10001857 / 10000000)) := by
  have h := reflection_log_4956_neg
  have he : Real.log (10001857 / 10000000) = -Real.log (10000000 / 10001857) := by
    rw [show ((10001857 / 10000000) : ℝ) = ((10000000 / 10001857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4957_neg : (185717 / 1000000000) ≤ -Real.log (9998143 / 10000000) ∧
    -Real.log (9998143 / 10000000) ≤ (92859 / 500000000) := by
  have h := checkLog_sound (w := (1857 / 19998143)) (n := 12)
    (lo := (185717 / 1000000000)) (hi := (92859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998143) = 1/(9998143 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4957 : Bounds (-92859 / 500000000) (-185717 / 1000000000) (Real.log (9998143 / 10000000)) := by
  have h := reflection_log_4957_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4958_neg : (44595749 / 500000000) ≤ -Real.log (100000 / 109329) ∧
    -Real.log (100000 / 109329) ≤ (89191499 / 1000000000) := by
  have h := checkLog_sound (w := (9329 / 209329)) (n := 12)
    (lo := (44595749 / 500000000)) (hi := (89191499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109329 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109329 / 100000) = 1/(100000 / 109329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4958 : Bounds (44595749 / 500000000) (89191499 / 1000000000) (Real.log (109329 / 100000)) := by
  have h := reflection_log_4958_neg
  have he : Real.log (109329 / 100000) = -Real.log (100000 / 109329) := by
    rw [show ((109329 / 100000) : ℝ) = ((100000 / 109329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4959_neg : (19586523 / 200000000) ≤ -Real.log (90671 / 100000) ∧
    -Real.log (90671 / 100000) ≤ (12241577 / 125000000) := by
  have h := checkLog_sound (w := (9329 / 190671)) (n := 12)
    (lo := (19586523 / 200000000)) (hi := (12241577 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90671) = 1/(90671 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4959 : Bounds (-12241577 / 125000000) (-19586523 / 200000000) (Real.log (90671 / 100000)) := by
  have h := reflection_log_4959_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4960_neg : (89407337 / 1000000000) ≤ -Real.log (500000 / 546763) ∧
    -Real.log (500000 / 546763) ≤ (44703669 / 500000000) := by
  have h := checkLog_sound (w := (46763 / 1046763)) (n := 12)
    (lo := (89407337 / 1000000000)) (hi := (44703669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546763 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546763 / 500000) = 1/(500000 / 546763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4960 : Bounds (89407337 / 1000000000) (44703669 / 500000000) (Real.log (546763 / 500000)) := by
  have h := reflection_log_4960_neg
  have he : Real.log (546763 / 500000) = -Real.log (500000 / 546763) := by
    rw [show ((546763 / 500000) : ℝ) = ((500000 / 546763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4961_neg : (9819293 / 100000000) ≤ -Real.log (453237 / 500000) ∧
    -Real.log (453237 / 500000) ≤ (98192931 / 1000000000) := by
  have h := checkLog_sound (w := (46763 / 953237)) (n := 12)
    (lo := (9819293 / 100000000)) (hi := (98192931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453237) = 1/(453237 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4961 : Bounds (-98192931 / 1000000000) (-9819293 / 100000000) (Real.log (453237 / 500000)) := by
  have h := reflection_log_4961_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4962_neg : (8785593 / 1000000000) ≤ -Real.log (247813221831 / 250000000000) ∧
    -Real.log (247813221831 / 250000000000) ≤ (4392797 / 500000000) := by
  have h := checkLog_sound (w := (2186778169 / 497813221831)) (n := 12)
    (lo := (8785593 / 1000000000)) (hi := (4392797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247813221831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247813221831) = 1/(247813221831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4962 : Bounds (-4392797 / 500000000) (-8785593 / 1000000000) (Real.log (247813221831 / 250000000000)) := by
  have h := reflection_log_4962_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4963_neg : (2185279 / 250000000) ≤ -Real.log (9912969759 / 10000000000) ∧
    -Real.log (9912969759 / 10000000000) ≤ (8741117 / 1000000000) := by
  have h := checkLog_sound (w := (87030241 / 19912969759)) (n := 12)
    (lo := (2185279 / 250000000)) (hi := (8741117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9912969759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9912969759) = 1/(9912969759 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4963 : Bounds (-8741117 / 1000000000) (-2185279 / 250000000) (Real.log (9912969759 / 10000000000)) := by
  have h := reflection_log_4963_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4964_neg : (93562057 / 500000000) ≤ -Real.log (500000000000 / 602888464889) ∧
    -Real.log (500000000000 / 602888464889) ≤ (37424823 / 200000000) := by
  have h := checkLog_sound (w := (102888464889 / 1102888464889)) (n := 12)
    (lo := (93562057 / 500000000)) (hi := (37424823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602888464889 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602888464889 / 500000000000) = 1/(500000000000 / 602888464889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4964 : Bounds (93562057 / 500000000) (37424823 / 200000000) (Real.log (602888464889 / 500000000000)) := by
  have h := reflection_log_4964_neg
  have he : Real.log (602888464889 / 500000000000) = -Real.log (500000000000 / 602888464889) := by
    rw [show ((602888464889 / 500000000000) : ℝ) = ((500000000000 / 602888464889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4965_neg : (46900067 / 250000000) ≤ -Real.log (250000000000 / 301587800643) ∧
    -Real.log (250000000000 / 301587800643) ≤ (187600269 / 1000000000) := by
  have h := checkLog_sound (w := (51587800643 / 551587800643)) (n := 12)
    (lo := (46900067 / 250000000)) (hi := (187600269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301587800643 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301587800643 / 250000000000) = 1/(250000000000 / 301587800643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4965 : Bounds (46900067 / 250000000) (187600269 / 1000000000) (Real.log (301587800643 / 250000000000)) := by
  have h := reflection_log_4965_neg
  have he : Real.log (301587800643 / 250000000000) = -Real.log (250000000000 / 301587800643) := by
    rw [show ((301587800643 / 250000000000) : ℝ) = ((250000000000 / 301587800643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4966_neg : (11736019 / 31250000) ≤ -Real.log (500000000000 / 727897838899) ∧
    -Real.log (500000000000 / 727897838899) ≤ (375552609 / 1000000000) := by
  have h := checkLog_sound (w := (227897838899 / 1227897838899)) (n := 12)
    (lo := (11736019 / 31250000)) (hi := (375552609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727897838899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727897838899 / 500000000000) = 1/(500000000000 / 727897838899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4966 : Bounds (11736019 / 31250000) (375552609 / 1000000000) (Real.log (727897838899 / 500000000000)) := by
  have h := reflection_log_4966_neg
  have he : Real.log (727897838899 / 500000000000) = -Real.log (500000000000 / 727897838899) := by
    rw [show ((727897838899 / 500000000000) : ℝ) = ((500000000000 / 727897838899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4967_neg : (375759747 / 1000000000) ≤ -Real.log (250000000000 / 364024315363) ∧
    -Real.log (250000000000 / 364024315363) ≤ (93939937 / 250000000) := by
  have h := checkLog_sound (w := (114024315363 / 614024315363)) (n := 12)
    (lo := (375759747 / 1000000000)) (hi := (93939937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364024315363 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(364024315363 / 250000000000) = 1/(250000000000 / 364024315363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4967 : Bounds (375759747 / 1000000000) (93939937 / 250000000) (Real.log (364024315363 / 250000000000)) := by
  have h := reflection_log_4967_neg
  have he : Real.log (364024315363 / 250000000000) = -Real.log (250000000000 / 364024315363) := by
    rw [show ((364024315363 / 250000000000) : ℝ) = ((250000000000 / 364024315363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4968_neg : (42604413 / 250000000) ≤ -Real.log (5000 / 5929) ∧
    -Real.log (5000 / 5929) ≤ (170417653 / 1000000000) := by
  have h := checkLog_sound (w := (929 / 10929)) (n := 12)
    (lo := (42604413 / 250000000)) (hi := (170417653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5929 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5929 / 5000) = 1/(5000 / 5929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4968 : Bounds (42604413 / 250000000) (170417653 / 1000000000) (Real.log (5929 / 5000)) := by
  have h := reflection_log_4968_neg
  have he : Real.log (5929 / 5000) = -Real.log (5000 / 5929) := by
    rw [show ((5929 / 5000) : ℝ) = ((5000 / 5929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4969_neg : (102774621 / 500000000) ≤ -Real.log (4071 / 5000) ∧
    -Real.log (4071 / 5000) ≤ (205549243 / 1000000000) := by
  have h := checkLog_sound (w := (929 / 9071)) (n := 12)
    (lo := (102774621 / 500000000)) (hi := (205549243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4071) = 1/(4071 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4969 : Bounds (-205549243 / 1000000000) (-102774621 / 500000000) (Real.log (4071 / 5000)) := by
  have h := reflection_log_4969_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4970_neg : (92891 / 500000000) ≤ -Real.log (5000000 / 5000929) ∧
    -Real.log (5000000 / 5000929) ≤ (185783 / 1000000000) := by
  have h := checkLog_sound (w := (929 / 10000929)) (n := 12)
    (lo := (92891 / 500000000)) (hi := (185783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000929 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000929 / 5000000) = 1/(5000000 / 5000929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4970 : Bounds (92891 / 500000000) (185783 / 1000000000) (Real.log (5000929 / 5000000)) := by
  have h := reflection_log_4970_neg
  have he : Real.log (5000929 / 5000000) = -Real.log (5000000 / 5000929) := by
    rw [show ((5000929 / 5000000) : ℝ) = ((5000000 / 5000929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4971_neg : (185817 / 1000000000) ≤ -Real.log (4999071 / 5000000) ∧
    -Real.log (4999071 / 5000000) ≤ (92909 / 500000000) := by
  have h := checkLog_sound (w := (929 / 9999071)) (n := 12)
    (lo := (185817 / 1000000000)) (hi := (92909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999071) = 1/(4999071 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4971 : Bounds (-92909 / 500000000) (-185817 / 1000000000) (Real.log (4999071 / 5000000)) := by
  have h := reflection_log_4971_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4972_neg : (17847629 / 200000000) ≤ -Real.log (1000000 / 1093341) ∧
    -Real.log (1000000 / 1093341) ≤ (44619073 / 500000000) := by
  have h := checkLog_sound (w := (93341 / 2093341)) (n := 12)
    (lo := (17847629 / 200000000)) (hi := (44619073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093341 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093341 / 1000000) = 1/(1000000 / 1093341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4972 : Bounds (17847629 / 200000000) (44619073 / 500000000) (Real.log (1093341 / 1000000)) := by
  have h := reflection_log_4972_neg
  have he : Real.log (1093341 / 1000000) = -Real.log (1000000 / 1093341) := by
    rw [show ((1093341 / 1000000) : ℝ) = ((1000000 / 1093341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4973_neg : (382769 / 3906250) ≤ -Real.log (906659 / 1000000) ∧
    -Real.log (906659 / 1000000) ≤ (19597773 / 200000000) := by
  have h := checkLog_sound (w := (93341 / 1906659)) (n := 12)
    (lo := (382769 / 3906250)) (hi := (19597773 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906659) = 1/(906659 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4973 : Bounds (-19597773 / 200000000) (-382769 / 3906250) (Real.log (906659 / 1000000)) := by
  have h := reflection_log_4973_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4974_neg : (44726987 / 500000000) ≤ -Real.log (1000000 / 1093577) ∧
    -Real.log (1000000 / 1093577) ≤ (3578159 / 40000000) := by
  have h := checkLog_sound (w := (93577 / 2093577)) (n := 12)
    (lo := (44726987 / 500000000)) (hi := (3578159 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093577 / 1000000) = 1/(1000000 / 1093577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4974 : Bounds (44726987 / 500000000) (3578159 / 40000000) (Real.log (1093577 / 1000000)) := by
  have h := reflection_log_4974_neg
  have he : Real.log (1093577 / 1000000) = -Real.log (1000000 / 1093577) := by
    rw [show ((1093577 / 1000000) : ℝ) = ((1000000 / 1093577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4975_neg : (49124597 / 500000000) ≤ -Real.log (906423 / 1000000) ∧
    -Real.log (906423 / 1000000) ≤ (19649839 / 200000000) := by
  have h := checkLog_sound (w := (93577 / 1906423)) (n := 12)
    (lo := (49124597 / 500000000)) (hi := (19649839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906423) = 1/(906423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4975 : Bounds (-19649839 / 200000000) (-49124597 / 500000000) (Real.log (906423 / 1000000)) := by
  have h := reflection_log_4975_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4976_neg : (8795219 / 1000000000) ≤ -Real.log (991243345071 / 1000000000000) ∧
    -Real.log (991243345071 / 1000000000000) ≤ (439761 / 50000000) := by
  have h := checkLog_sound (w := (8756654929 / 1991243345071)) (n := 12)
    (lo := (8795219 / 1000000000)) (hi := (439761 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991243345071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991243345071) = 1/(991243345071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4976 : Bounds (-439761 / 50000000) (-8795219 / 1000000000) (Real.log (991243345071 / 1000000000000)) := by
  have h := reflection_log_4976_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4977_neg : (4375359 / 500000000) ≤ -Real.log (991287457719 / 1000000000000) ∧
    -Real.log (991287457719 / 1000000000000) ≤ (8750719 / 1000000000) := by
  have h := checkLog_sound (w := (8712542281 / 1991287457719)) (n := 12)
    (lo := (4375359 / 500000000)) (hi := (8750719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991287457719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991287457719) = 1/(991287457719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4977 : Bounds (-8750719 / 1000000000) (-4375359 / 500000000) (Real.log (991287457719 / 1000000000000)) := by
  have h := reflection_log_4977_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4978_neg : (18722701 / 100000000) ≤ -Real.log (50000000000 / 60295050289) ∧
    -Real.log (50000000000 / 60295050289) ≤ (187227011 / 1000000000) := by
  have h := checkLog_sound (w := (10295050289 / 110295050289)) (n := 12)
    (lo := (18722701 / 100000000)) (hi := (187227011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60295050289 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60295050289 / 50000000000) = 1/(50000000000 / 60295050289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4978 : Bounds (18722701 / 100000000) (187227011 / 1000000000) (Real.log (60295050289 / 50000000000)) := by
  have h := reflection_log_4978_neg
  have he : Real.log (60295050289 / 50000000000) = -Real.log (50000000000 / 60295050289) := by
    rw [show ((60295050289 / 50000000000) : ℝ) = ((50000000000 / 60295050289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4979_neg : (187703169 / 1000000000) ≤ -Real.log (100000000000 / 120647534319) ∧
    -Real.log (100000000000 / 120647534319) ≤ (18770317 / 100000000) := by
  have h := checkLog_sound (w := (20647534319 / 220647534319)) (n := 12)
    (lo := (187703169 / 1000000000)) (hi := (18770317 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120647534319 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120647534319 / 100000000000) = 1/(100000000000 / 120647534319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4979 : Bounds (187703169 / 1000000000) (18770317 / 100000000) (Real.log (120647534319 / 100000000000)) := by
  have h := reflection_log_4979_neg
  have he : Real.log (120647534319 / 100000000000) = -Real.log (100000000000 / 120647534319) := by
    rw [show ((120647534319 / 100000000000) : ℝ) = ((100000000000 / 120647534319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4980_neg : (375759747 / 1000000000) ≤ -Real.log (20000000000 / 29121945229) ∧
    -Real.log (20000000000 / 29121945229) ≤ (93939937 / 250000000) := by
  have h := checkLog_sound (w := (9121945229 / 49121945229)) (n := 12)
    (lo := (375759747 / 1000000000)) (hi := (93939937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29121945229 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29121945229 / 20000000000) = 1/(20000000000 / 29121945229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4980 : Bounds (375759747 / 1000000000) (93939937 / 250000000) (Real.log (29121945229 / 20000000000)) := by
  have h := reflection_log_4980_neg
  have he : Real.log (29121945229 / 20000000000) = -Real.log (20000000000 / 29121945229) := by
    rw [show ((29121945229 / 20000000000) : ℝ) = ((20000000000 / 29121945229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4981_neg : (75193379 / 200000000) ≤ -Real.log (500000000000 / 728199459593) ∧
    -Real.log (500000000000 / 728199459593) ≤ (23497931 / 62500000) := by
  have h := checkLog_sound (w := (228199459593 / 1228199459593)) (n := 12)
    (lo := (75193379 / 200000000)) (hi := (23497931 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728199459593 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728199459593 / 500000000000) = 1/(500000000000 / 728199459593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4981 : Bounds (75193379 / 200000000) (23497931 / 62500000) (Real.log (728199459593 / 500000000000)) := by
  have h := reflection_log_4981_neg
  have he : Real.log (728199459593 / 500000000000) = -Real.log (500000000000 / 728199459593) := by
    rw [show ((728199459593 / 500000000000) : ℝ) = ((500000000000 / 728199459593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4982_neg : (170501979 / 1000000000) ≤ -Real.log (10000 / 11859) ∧
    -Real.log (10000 / 11859) ≤ (8525099 / 50000000) := by
  have h := checkLog_sound (w := (1859 / 21859)) (n := 12)
    (lo := (170501979 / 1000000000)) (hi := (8525099 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11859 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11859 / 10000) = 1/(10000 / 11859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4982 : Bounds (170501979 / 1000000000) (8525099 / 50000000) (Real.log (11859 / 10000)) := by
  have h := reflection_log_4982_neg
  have he : Real.log (11859 / 10000) = -Real.log (10000 / 11859) := by
    rw [show ((11859 / 10000) : ℝ) = ((10000 / 11859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4983_neg : (20567207 / 100000000) ≤ -Real.log (8141 / 10000) ∧
    -Real.log (8141 / 10000) ≤ (205672071 / 1000000000) := by
  have h := checkLog_sound (w := (1859 / 18141)) (n := 12)
    (lo := (20567207 / 100000000)) (hi := (205672071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8141) = 1/(8141 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4983 : Bounds (-205672071 / 1000000000) (-20567207 / 100000000) (Real.log (8141 / 10000)) := by
  have h := reflection_log_4983_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4984_neg : (92941 / 500000000) ≤ -Real.log (10000000 / 10001859) ∧
    -Real.log (10000000 / 10001859) ≤ (185883 / 1000000000) := by
  have h := checkLog_sound (w := (1859 / 20001859)) (n := 12)
    (lo := (92941 / 500000000)) (hi := (185883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001859 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001859 / 10000000) = 1/(10000000 / 10001859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4984 : Bounds (92941 / 500000000) (185883 / 1000000000) (Real.log (10001859 / 10000000)) := by
  have h := reflection_log_4984_neg
  have he : Real.log (10001859 / 10000000) = -Real.log (10000000 / 10001859) := by
    rw [show ((10001859 / 10000000) : ℝ) = ((10000000 / 10001859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4985_neg : (185917 / 1000000000) ≤ -Real.log (9998141 / 10000000) ∧
    -Real.log (9998141 / 10000000) ≤ (92959 / 500000000) := by
  have h := checkLog_sound (w := (1859 / 19998141)) (n := 12)
    (lo := (185917 / 1000000000)) (hi := (92959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998141) = 1/(9998141 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4985 : Bounds (-92959 / 500000000) (-185917 / 1000000000) (Real.log (9998141 / 10000000)) := by
  have h := reflection_log_4985_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4986_neg : (22320969 / 250000000) ≤ -Real.log (1000000 / 1093391) ∧
    -Real.log (1000000 / 1093391) ≤ (89283877 / 1000000000) := by
  have h := checkLog_sound (w := (93391 / 2093391)) (n := 12)
    (lo := (22320969 / 250000000)) (hi := (89283877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093391 / 1000000) = 1/(1000000 / 1093391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4986 : Bounds (22320969 / 250000000) (89283877 / 1000000000) (Real.log (1093391 / 1000000)) := by
  have h := reflection_log_4986_neg
  have he : Real.log (1093391 / 1000000) = -Real.log (1000000 / 1093391) := by
    rw [show ((1093391 / 1000000) : ℝ) = ((1000000 / 1093391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4987_neg : (98044013 / 1000000000) ≤ -Real.log (906609 / 1000000) ∧
    -Real.log (906609 / 1000000) ≤ (49022007 / 500000000) := by
  have h := checkLog_sound (w := (93391 / 1906609)) (n := 12)
    (lo := (98044013 / 1000000000)) (hi := (49022007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 906609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 906609) = 1/(906609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4987 : Bounds (-49022007 / 500000000) (-98044013 / 1000000000) (Real.log (906609 / 1000000)) := by
  have h := reflection_log_4987_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4988_neg : (89500609 / 1000000000) ≤ -Real.log (250000 / 273407) ∧
    -Real.log (250000 / 273407) ≤ (8950061 / 100000000) := by
  have h := checkLog_sound (w := (23407 / 523407)) (n := 12)
    (lo := (89500609 / 1000000000)) (hi := (8950061 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273407 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273407 / 250000) = 1/(250000 / 273407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4988 : Bounds (89500609 / 1000000000) (8950061 / 100000000) (Real.log (273407 / 250000)) := by
  have h := reflection_log_4988_neg
  have he : Real.log (273407 / 250000) = -Real.log (250000 / 273407) := by
    rw [show ((273407 / 250000) : ℝ) = ((250000 / 273407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4989_neg : (98305461 / 1000000000) ≤ -Real.log (226593 / 250000) ∧
    -Real.log (226593 / 250000) ≤ (49152731 / 500000000) := by
  have h := checkLog_sound (w := (23407 / 476593)) (n := 12)
    (lo := (98305461 / 1000000000)) (hi := (49152731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226593) = 1/(226593 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4989 : Bounds (-49152731 / 500000000) (-98305461 / 1000000000) (Real.log (226593 / 250000)) := by
  have h := reflection_log_4989_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4990_neg : (8804851 / 1000000000) ≤ -Real.log (61952112351 / 62500000000) ∧
    -Real.log (61952112351 / 62500000000) ≤ (2201213 / 250000000) := by
  have h := checkLog_sound (w := (547887649 / 124452112351)) (n := 12)
    (lo := (8804851 / 1000000000)) (hi := (2201213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61952112351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61952112351) = 1/(61952112351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4990 : Bounds (-2201213 / 250000000) (-8804851 / 1000000000) (Real.log (61952112351 / 62500000000)) := by
  have h := reflection_log_4990_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4991_neg : (8760137 / 1000000000) ≤ -Real.log (991278121119 / 1000000000000) ∧
    -Real.log (991278121119 / 1000000000000) ≤ (4380069 / 500000000) := by
  have h := checkLog_sound (w := (8721878881 / 1991278121119)) (n := 12)
    (lo := (8760137 / 1000000000)) (hi := (4380069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991278121119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991278121119) = 1/(991278121119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4991 : Bounds (-4380069 / 500000000) (-8760137 / 1000000000) (Real.log (991278121119 / 1000000000000)) := by
  have h := reflection_log_4991_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
