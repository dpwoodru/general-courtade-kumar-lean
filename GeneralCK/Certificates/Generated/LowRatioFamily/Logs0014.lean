import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_896_neg : (332876 / 1953125) ≤ -Real.log (8433 / 10000) ∧
    -Real.log (8433 / 10000) ≤ (170432513 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 18433)) (n := 12)
    (lo := (332876 / 1953125)) (hi := (170432513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8433) = 1/(8433 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_896 : Bounds (-170432513 / 1000000000) (-332876 / 1953125) (Real.log (8433 / 10000)) := by
  have h := reflection_log_896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_897_neg : (156687 / 1000000000) ≤ -Real.log (10000000 / 10001567) ∧
    -Real.log (10000000 / 10001567) ≤ (9793 / 62500000) := by
  have h := checkLog_sound (w := (1567 / 20001567)) (n := 12)
    (lo := (156687 / 1000000000)) (hi := (9793 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001567 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001567 / 10000000) = 1/(10000000 / 10001567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_897 : Bounds (156687 / 1000000000) (9793 / 62500000) (Real.log (10001567 / 10000000)) := by
  have h := reflection_log_897_neg
  have he : Real.log (10001567 / 10000000) = -Real.log (10000000 / 10001567) := by
    rw [show ((10001567 / 10000000) : ℝ) = ((10000000 / 10001567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_898_neg : (19589 / 125000000) ≤ -Real.log (9998433 / 10000000) ∧
    -Real.log (9998433 / 10000000) ≤ (156713 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 19998433)) (n := 12)
    (lo := (19589 / 125000000)) (hi := (156713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998433) = 1/(9998433 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_898 : Bounds (-156713 / 1000000000) (-19589 / 125000000) (Real.log (9998433 / 10000000)) := by
  have h := reflection_log_898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_899_neg : (75636089 / 1000000000) ≤ -Real.log (100000 / 107857) ∧
    -Real.log (100000 / 107857) ≤ (7563609 / 100000000) := by
  have h := checkLog_sound (w := (7857 / 207857)) (n := 12)
    (lo := (75636089 / 1000000000)) (hi := (7563609 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107857 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107857 / 100000) = 1/(100000 / 107857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_899 : Bounds (75636089 / 1000000000) (7563609 / 100000000) (Real.log (107857 / 100000)) := by
  have h := reflection_log_899_neg
  have he : Real.log (107857 / 100000) = -Real.log (100000 / 107857) := by
    rw [show ((107857 / 100000) : ℝ) = ((100000 / 107857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_900_neg : (81828467 / 1000000000) ≤ -Real.log (92143 / 100000) ∧
    -Real.log (92143 / 100000) ≤ (20457117 / 250000000) := by
  have h := checkLog_sound (w := (7857 / 192143)) (n := 12)
    (lo := (81828467 / 1000000000)) (hi := (20457117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 92143) = 1/(92143 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_900 : Bounds (-20457117 / 250000000) (-81828467 / 1000000000) (Real.log (92143 / 100000)) := by
  have h := reflection_log_900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_901_neg : (75828919 / 1000000000) ≤ -Real.log (500000 / 539389) ∧
    -Real.log (500000 / 539389) ≤ (1895723 / 25000000) := by
  have h := checkLog_sound (w := (39389 / 1039389)) (n := 12)
    (lo := (75828919 / 1000000000)) (hi := (1895723 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539389 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539389 / 500000) = 1/(500000 / 539389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_901 : Bounds (75828919 / 1000000000) (1895723 / 25000000) (Real.log (539389 / 500000)) := by
  have h := reflection_log_901_neg
  have he : Real.log (539389 / 500000) = -Real.log (500000 / 539389) := by
    rw [show ((539389 / 500000) : ℝ) = ((500000 / 539389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_902_neg : (82054229 / 1000000000) ≤ -Real.log (460611 / 500000) ∧
    -Real.log (460611 / 500000) ≤ (8205423 / 100000000) := by
  have h := checkLog_sound (w := (39389 / 960611)) (n := 12)
    (lo := (82054229 / 1000000000)) (hi := (8205423 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460611) = 1/(460611 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_902 : Bounds (-8205423 / 100000000) (-82054229 / 1000000000) (Real.log (460611 / 500000)) := by
  have h := reflection_log_902_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_903_neg : (622531 / 100000000) ≤ -Real.log (248448506679 / 250000000000) ∧
    -Real.log (248448506679 / 250000000000) ≤ (6225311 / 1000000000) := by
  have h := checkLog_sound (w := (1551493321 / 498448506679)) (n := 12)
    (lo := (622531 / 100000000)) (hi := (6225311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248448506679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248448506679) = 1/(248448506679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_903 : Bounds (-6225311 / 1000000000) (-622531 / 100000000) (Real.log (248448506679 / 250000000000)) := by
  have h := reflection_log_903_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_904_neg : (3096189 / 500000000) ≤ -Real.log (9938267551 / 10000000000) ∧
    -Real.log (9938267551 / 10000000000) ≤ (6192379 / 1000000000) := by
  have h := checkLog_sound (w := (61732449 / 19938267551)) (n := 12)
    (lo := (3096189 / 500000000)) (hi := (6192379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9938267551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9938267551) = 1/(9938267551 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_904 : Bounds (-6192379 / 1000000000) (-3096189 / 500000000) (Real.log (9938267551 / 10000000000)) := by
  have h := reflection_log_904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_905_neg : (157464557 / 1000000000) ≤ -Real.log (12500000000 / 14631740881) ∧
    -Real.log (12500000000 / 14631740881) ≤ (78732279 / 500000000) := by
  have h := checkLog_sound (w := (2131740881 / 27131740881)) (n := 12)
    (lo := (157464557 / 1000000000)) (hi := (78732279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14631740881 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14631740881 / 12500000000) = 1/(12500000000 / 14631740881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_905 : Bounds (157464557 / 1000000000) (78732279 / 500000000) (Real.log (14631740881 / 12500000000)) := by
  have h := reflection_log_905_neg
  have he : Real.log (14631740881 / 12500000000) = -Real.log (12500000000 / 14631740881) := by
    rw [show ((14631740881 / 12500000000) : ℝ) = ((12500000000 / 14631740881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_906_neg : (39470787 / 250000000) ≤ -Real.log (500000000000 / 585514675073) ∧
    -Real.log (500000000000 / 585514675073) ≤ (157883149 / 1000000000) := by
  have h := checkLog_sound (w := (85514675073 / 1085514675073)) (n := 12)
    (lo := (39470787 / 250000000)) (hi := (157883149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585514675073 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585514675073 / 500000000000) = 1/(500000000000 / 585514675073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_906 : Bounds (39470787 / 250000000) (157883149 / 1000000000) (Real.log (585514675073 / 500000000000)) := by
  have h := reflection_log_906_neg
  have he : Real.log (585514675073 / 500000000000) = -Real.log (500000000000 / 585514675073) := by
    rw [show ((585514675073 / 500000000000) : ℝ) = ((500000000000 / 585514675073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_907_neg : (78949651 / 250000000) ≤ -Real.log (500000000000 / 685677021579) ∧
    -Real.log (500000000000 / 685677021579) ≤ (63159721 / 200000000) := by
  have h := checkLog_sound (w := (185677021579 / 1185677021579)) (n := 12)
    (lo := (78949651 / 250000000)) (hi := (63159721 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685677021579 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685677021579 / 500000000000) = 1/(500000000000 / 685677021579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_907 : Bounds (78949651 / 250000000) (63159721 / 200000000) (Real.log (685677021579 / 500000000000)) := by
  have h := reflection_log_907_neg
  have he : Real.log (685677021579 / 500000000000) = -Real.log (500000000000 / 685677021579) := by
    rw [show ((685677021579 / 500000000000) : ℝ) = ((500000000000 / 685677021579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_908_neg : (63200727 / 200000000) ≤ -Real.log (400000000 / 548654097) ∧
    -Real.log (400000000 / 548654097) ≤ (79000909 / 250000000) := by
  have h := checkLog_sound (w := (148654097 / 948654097)) (n := 12)
    (lo := (63200727 / 200000000)) (hi := (79000909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548654097 / 400000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548654097 / 400000000) = 1/(400000000 / 548654097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_908 : Bounds (63200727 / 200000000) (79000909 / 250000000) (Real.log (548654097 / 400000000)) := by
  have h := reflection_log_908_neg
  have he : Real.log (548654097 / 400000000) = -Real.log (400000000 / 548654097) := by
    rw [show ((548654097 / 400000000) : ℝ) = ((400000000 / 548654097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_909_neg : (36414393 / 250000000) ≤ -Real.log (625 / 723) ∧
    -Real.log (625 / 723) ≤ (145657573 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 674)) (n := 12)
    (lo := (36414393 / 250000000)) (hi := (145657573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723 / 625) = 1/(625 / 723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_909 : Bounds (36414393 / 250000000) (145657573 / 1000000000) (Real.log (723 / 625)) := by
  have h := reflection_log_909_neg
  have he : Real.log (723 / 625) = -Real.log (625 / 723) := by
    rw [show ((723 / 625) : ℝ) = ((625 / 723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_910_neg : (170551101 / 1000000000) ≤ -Real.log (527 / 625) ∧
    -Real.log (527 / 625) ≤ (85275551 / 500000000) := by
  have h := checkLog_sound (w := (49 / 576)) (n := 12)
    (lo := (170551101 / 1000000000)) (hi := (85275551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 527) = 1/(527 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_910 : Bounds (-85275551 / 500000000) (-170551101 / 1000000000) (Real.log (527 / 625)) := by
  have h := reflection_log_910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_911_neg : (156787 / 1000000000) ≤ -Real.log (312500 / 312549) ∧
    -Real.log (312500 / 312549) ≤ (39197 / 250000000) := by
  have h := checkLog_sound (w := (49 / 625049)) (n := 12)
    (lo := (156787 / 1000000000)) (hi := (39197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312549 / 312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312549 / 312500) = 1/(312500 / 312549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_911 : Bounds (156787 / 1000000000) (39197 / 250000000) (Real.log (312549 / 312500)) := by
  have h := reflection_log_911_neg
  have he : Real.log (312549 / 312500) = -Real.log (312500 / 312549) := by
    rw [show ((312549 / 312500) : ℝ) = ((312500 / 312549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_912_neg : (39203 / 250000000) ≤ -Real.log (312451 / 312500) ∧
    -Real.log (312451 / 312500) ≤ (156813 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 624951)) (n := 12)
    (lo := (39203 / 250000000)) (hi := (156813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312500 / 312451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312500 / 312451) = 1/(312451 / 312500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_912 : Bounds (-156813 / 1000000000) (-39203 / 250000000) (Real.log (312451 / 312500)) := by
  have h := reflection_log_912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_913_neg : (75683373 / 1000000000) ≤ -Real.log (1000000 / 1078621) ∧
    -Real.log (1000000 / 1078621) ≤ (37841687 / 500000000) := by
  have h := checkLog_sound (w := (78621 / 2078621)) (n := 12)
    (lo := (75683373 / 1000000000)) (hi := (37841687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078621 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078621 / 1000000) = 1/(1000000 / 1078621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_913 : Bounds (75683373 / 1000000000) (37841687 / 500000000) (Real.log (1078621 / 1000000)) := by
  have h := reflection_log_913_neg
  have he : Real.log (1078621 / 1000000) = -Real.log (1000000 / 1078621) := by
    rw [show ((1078621 / 1000000) : ℝ) = ((1000000 / 1078621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_914_neg : (40941909 / 500000000) ≤ -Real.log (921379 / 1000000) ∧
    -Real.log (921379 / 1000000) ≤ (81883819 / 1000000000) := by
  have h := checkLog_sound (w := (78621 / 1921379)) (n := 12)
    (lo := (40941909 / 500000000)) (hi := (81883819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921379) = 1/(921379 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_914 : Bounds (-81883819 / 1000000000) (-40941909 / 500000000) (Real.log (921379 / 1000000)) := by
  have h := reflection_log_914_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_915_neg : (75876193 / 1000000000) ≤ -Real.log (1000000 / 1078829) ∧
    -Real.log (1000000 / 1078829) ≤ (37938097 / 500000000) := by
  have h := checkLog_sound (w := (78829 / 2078829)) (n := 12)
    (lo := (75876193 / 1000000000)) (hi := (37938097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078829 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078829 / 1000000) = 1/(1000000 / 1078829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_915 : Bounds (75876193 / 1000000000) (37938097 / 500000000) (Real.log (1078829 / 1000000)) := by
  have h := reflection_log_915_neg
  have he : Real.log (1078829 / 1000000) = -Real.log (1000000 / 1078829) := by
    rw [show ((1078829 / 1000000) : ℝ) = ((1000000 / 1078829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_916_neg : (10263699 / 125000000) ≤ -Real.log (921171 / 1000000) ∧
    -Real.log (921171 / 1000000) ≤ (82109593 / 1000000000) := by
  have h := checkLog_sound (w := (78829 / 1921171)) (n := 12)
    (lo := (10263699 / 125000000)) (hi := (82109593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921171) = 1/(921171 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_916 : Bounds (-82109593 / 1000000000) (-10263699 / 125000000) (Real.log (921171 / 1000000)) := by
  have h := reflection_log_916_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_917_neg : (3116699 / 500000000) ≤ -Real.log (993785988759 / 1000000000000) ∧
    -Real.log (993785988759 / 1000000000000) ≤ (6233399 / 1000000000) := by
  have h := checkLog_sound (w := (6214011241 / 1993785988759)) (n := 12)
    (lo := (3116699 / 500000000)) (hi := (6233399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993785988759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993785988759) = 1/(993785988759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_917 : Bounds (-6233399 / 1000000000) (-3116699 / 500000000) (Real.log (993785988759 / 1000000000000)) := by
  have h := reflection_log_917_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_918_neg : (1550111 / 250000000) ≤ -Real.log (993818738359 / 1000000000000) ∧
    -Real.log (993818738359 / 1000000000000) ≤ (1240089 / 200000000) := by
  have h := checkLog_sound (w := (6181261641 / 1993818738359)) (n := 12)
    (lo := (1550111 / 250000000)) (hi := (1240089 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993818738359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993818738359) = 1/(993818738359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_918 : Bounds (-1240089 / 200000000) (-1550111 / 250000000) (Real.log (993818738359 / 1000000000000)) := by
  have h := reflection_log_918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_919_neg : (157567191 / 1000000000) ≤ -Real.log (100000000000 / 117065941377) ∧
    -Real.log (100000000000 / 117065941377) ≤ (19695899 / 125000000) := by
  have h := checkLog_sound (w := (17065941377 / 217065941377)) (n := 12)
    (lo := (157567191 / 1000000000)) (hi := (19695899 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117065941377 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117065941377 / 100000000000) = 1/(100000000000 / 117065941377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_919 : Bounds (157567191 / 1000000000) (19695899 / 125000000) (Real.log (117065941377 / 100000000000)) := by
  have h := reflection_log_919_neg
  have he : Real.log (117065941377 / 100000000000) = -Real.log (100000000000 / 117065941377) := by
    rw [show ((117065941377 / 100000000000) : ℝ) = ((100000000000 / 117065941377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_920_neg : (31597157 / 200000000) ≤ -Real.log (62500000000 / 73196846731) ∧
    -Real.log (62500000000 / 73196846731) ≤ (78992893 / 500000000) := by
  have h := checkLog_sound (w := (10696846731 / 135696846731)) (n := 12)
    (lo := (31597157 / 200000000)) (hi := (78992893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73196846731 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73196846731 / 62500000000) = 1/(62500000000 / 73196846731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_920 : Bounds (31597157 / 200000000) (78992893 / 500000000) (Real.log (73196846731 / 62500000000)) := by
  have h := reflection_log_920_neg
  have he : Real.log (73196846731 / 62500000000) = -Real.log (62500000000 / 73196846731) := by
    rw [show ((73196846731 / 62500000000) : ℝ) = ((62500000000 / 73196846731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_921_neg : (63200727 / 200000000) ≤ -Real.log (500000000000 / 685817621249) ∧
    -Real.log (500000000000 / 685817621249) ≤ (79000909 / 250000000) := by
  have h := checkLog_sound (w := (185817621249 / 1185817621249)) (n := 12)
    (lo := (63200727 / 200000000)) (hi := (79000909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685817621249 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685817621249 / 500000000000) = 1/(500000000000 / 685817621249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_921 : Bounds (63200727 / 200000000) (79000909 / 250000000) (Real.log (685817621249 / 500000000000)) := by
  have h := reflection_log_921_neg
  have he : Real.log (685817621249 / 500000000000) = -Real.log (500000000000 / 685817621249) := by
    rw [show ((685817621249 / 500000000000) : ℝ) = ((500000000000 / 685817621249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_922_neg : (316208673 / 1000000000) ≤ -Real.log (50000000000 / 68595825427) ∧
    -Real.log (50000000000 / 68595825427) ≤ (158104337 / 500000000) := by
  have h := checkLog_sound (w := (18595825427 / 118595825427)) (n := 12)
    (lo := (316208673 / 1000000000)) (hi := (158104337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68595825427 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68595825427 / 50000000000) = 1/(50000000000 / 68595825427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_922 : Bounds (316208673 / 1000000000) (158104337 / 500000000) (Real.log (68595825427 / 50000000000)) := by
  have h := reflection_log_922_neg
  have he : Real.log (68595825427 / 50000000000) = -Real.log (50000000000 / 68595825427) := by
    rw [show ((68595825427 / 50000000000) : ℝ) = ((50000000000 / 68595825427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_923_neg : (72872007 / 500000000) ≤ -Real.log (10000 / 11569) ∧
    -Real.log (10000 / 11569) ≤ (29148803 / 200000000) := by
  have h := checkLog_sound (w := (1569 / 21569)) (n := 12)
    (lo := (72872007 / 500000000)) (hi := (29148803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11569 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11569 / 10000) = 1/(10000 / 11569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_923 : Bounds (72872007 / 500000000) (29148803 / 200000000) (Real.log (11569 / 10000)) := by
  have h := reflection_log_923_neg
  have he : Real.log (11569 / 10000) = -Real.log (10000 / 11569) := by
    rw [show ((11569 / 10000) : ℝ) = ((10000 / 11569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_924_neg : (21333713 / 125000000) ≤ -Real.log (8431 / 10000) ∧
    -Real.log (8431 / 10000) ≤ (34133941 / 200000000) := by
  have h := checkLog_sound (w := (1569 / 18431)) (n := 12)
    (lo := (21333713 / 125000000)) (hi := (34133941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8431) = 1/(8431 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_924 : Bounds (-34133941 / 200000000) (-21333713 / 125000000) (Real.log (8431 / 10000)) := by
  have h := reflection_log_924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_925_neg : (156887 / 1000000000) ≤ -Real.log (10000000 / 10001569) ∧
    -Real.log (10000000 / 10001569) ≤ (19611 / 125000000) := by
  have h := checkLog_sound (w := (1569 / 20001569)) (n := 12)
    (lo := (156887 / 1000000000)) (hi := (19611 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001569 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001569 / 10000000) = 1/(10000000 / 10001569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_925 : Bounds (156887 / 1000000000) (19611 / 125000000) (Real.log (10001569 / 10000000)) := by
  have h := reflection_log_925_neg
  have he : Real.log (10001569 / 10000000) = -Real.log (10000000 / 10001569) := by
    rw [show ((10001569 / 10000000) : ℝ) = ((10000000 / 10001569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_926_neg : (9807 / 62500000) ≤ -Real.log (9998431 / 10000000) ∧
    -Real.log (9998431 / 10000000) ≤ (156913 / 1000000000) := by
  have h := checkLog_sound (w := (1569 / 19998431)) (n := 12)
    (lo := (9807 / 62500000)) (hi := (156913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998431) = 1/(9998431 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_926 : Bounds (-156913 / 1000000000) (-9807 / 62500000) (Real.log (9998431 / 10000000)) := by
  have h := reflection_log_926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_927_neg : (37865327 / 500000000) ≤ -Real.log (62500 / 67417) ∧
    -Real.log (62500 / 67417) ≤ (15146131 / 200000000) := by
  have h := checkLog_sound (w := (4917 / 129917)) (n := 12)
    (lo := (37865327 / 500000000)) (hi := (15146131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67417 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67417 / 62500) = 1/(62500 / 67417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_927 : Bounds (37865327 / 500000000) (15146131 / 200000000) (Real.log (67417 / 62500)) := by
  have h := reflection_log_927_neg
  have he : Real.log (67417 / 62500) = -Real.log (62500 / 67417) := by
    rw [show ((67417 / 62500) : ℝ) = ((62500 / 67417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_928_neg : (81939171 / 1000000000) ≤ -Real.log (57583 / 62500) ∧
    -Real.log (57583 / 62500) ≤ (20484793 / 250000000) := by
  have h := checkLog_sound (w := (4917 / 120083)) (n := 12)
    (lo := (81939171 / 1000000000)) (hi := (20484793 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57583) = 1/(57583 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_928 : Bounds (-20484793 / 250000000) (-81939171 / 1000000000) (Real.log (57583 / 62500)) := by
  have h := reflection_log_928_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_929_neg : (75922539 / 1000000000) ≤ -Real.log (1000000 / 1078879) ∧
    -Real.log (1000000 / 1078879) ≤ (3796127 / 50000000) := by
  have h := checkLog_sound (w := (78879 / 2078879)) (n := 12)
    (lo := (75922539 / 1000000000)) (hi := (3796127 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078879 / 1000000) = 1/(1000000 / 1078879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_929 : Bounds (75922539 / 1000000000) (3796127 / 50000000) (Real.log (1078879 / 1000000)) := by
  have h := reflection_log_929_neg
  have he : Real.log (1078879 / 1000000) = -Real.log (1000000 / 1078879) := by
    rw [show ((1078879 / 1000000) : ℝ) = ((1000000 / 1078879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_930_neg : (2567621 / 31250000) ≤ -Real.log (921121 / 1000000) ∧
    -Real.log (921121 / 1000000) ≤ (82163873 / 1000000000) := by
  have h := checkLog_sound (w := (78879 / 1921121)) (n := 12)
    (lo := (2567621 / 31250000)) (hi := (82163873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921121) = 1/(921121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_930 : Bounds (-82163873 / 1000000000) (-2567621 / 31250000) (Real.log (921121 / 1000000)) := by
  have h := reflection_log_930_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_931_neg : (6241333 / 1000000000) ≤ -Real.log (993778103359 / 1000000000000) ∧
    -Real.log (993778103359 / 1000000000000) ≤ (3120667 / 500000000) := by
  have h := checkLog_sound (w := (6221896641 / 1993778103359)) (n := 12)
    (lo := (6241333 / 1000000000)) (hi := (3120667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993778103359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993778103359) = 1/(993778103359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_931 : Bounds (-3120667 / 500000000) (-6241333 / 1000000000) (Real.log (993778103359 / 1000000000000)) := by
  have h := reflection_log_931_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_932_neg : (1552129 / 250000000) ≤ -Real.log (3882073111 / 3906250000) ∧
    -Real.log (3882073111 / 3906250000) ≤ (6208517 / 1000000000) := by
  have h := checkLog_sound (w := (24176889 / 7788323111)) (n := 12)
    (lo := (1552129 / 250000000)) (hi := (6208517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3882073111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3882073111) = 1/(3882073111 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_932 : Bounds (-6208517 / 1000000000) (-1552129 / 250000000) (Real.log (3882073111 / 3906250000)) := by
  have h := reflection_log_932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_933_neg : (78834913 / 500000000) ≤ -Real.log (500000000000 / 585389785179) ∧
    -Real.log (500000000000 / 585389785179) ≤ (157669827 / 1000000000) := by
  have h := checkLog_sound (w := (85389785179 / 1085389785179)) (n := 12)
    (lo := (78834913 / 500000000)) (hi := (157669827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585389785179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585389785179 / 500000000000) = 1/(500000000000 / 585389785179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_933 : Bounds (78834913 / 500000000) (157669827 / 1000000000) (Real.log (585389785179 / 500000000000)) := by
  have h := reflection_log_933_neg
  have he : Real.log (585389785179 / 500000000000) = -Real.log (500000000000 / 585389785179) := by
    rw [show ((585389785179 / 500000000000) : ℝ) = ((500000000000 / 585389785179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_934_neg : (158086411 / 1000000000) ≤ -Real.log (125000000000 / 146408425169) ∧
    -Real.log (125000000000 / 146408425169) ≤ (39521603 / 250000000) := by
  have h := checkLog_sound (w := (21408425169 / 271408425169)) (n := 12)
    (lo := (158086411 / 1000000000)) (hi := (39521603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146408425169 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146408425169 / 125000000000) = 1/(125000000000 / 146408425169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_934 : Bounds (158086411 / 1000000000) (39521603 / 250000000) (Real.log (146408425169 / 125000000000)) := by
  have h := reflection_log_934_neg
  have he : Real.log (146408425169 / 125000000000) = -Real.log (125000000000 / 146408425169) := by
    rw [show ((146408425169 / 125000000000) : ℝ) = ((125000000000 / 146408425169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_935_neg : (316208673 / 1000000000) ≤ -Real.log (500000000000 / 685958254269) ∧
    -Real.log (500000000000 / 685958254269) ≤ (158104337 / 500000000) := by
  have h := checkLog_sound (w := (185958254269 / 1185958254269)) (n := 12)
    (lo := (316208673 / 1000000000)) (hi := (158104337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685958254269 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685958254269 / 500000000000) = 1/(500000000000 / 685958254269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_935 : Bounds (316208673 / 1000000000) (158104337 / 500000000) (Real.log (685958254269 / 500000000000)) := by
  have h := reflection_log_935_neg
  have he : Real.log (685958254269 / 500000000000) = -Real.log (500000000000 / 685958254269) := by
    rw [show ((685958254269 / 500000000000) : ℝ) = ((500000000000 / 685958254269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_936_neg : (158206859 / 500000000) ≤ -Real.log (10000000000 / 13721978413) ∧
    -Real.log (10000000000 / 13721978413) ≤ (316413719 / 1000000000) := by
  have h := checkLog_sound (w := (3721978413 / 23721978413)) (n := 12)
    (lo := (158206859 / 500000000)) (hi := (316413719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13721978413 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13721978413 / 10000000000) = 1/(10000000000 / 13721978413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_936 : Bounds (158206859 / 500000000) (316413719 / 1000000000) (Real.log (13721978413 / 10000000000)) := by
  have h := reflection_log_936_neg
  have he : Real.log (13721978413 / 10000000000) = -Real.log (10000000000 / 13721978413) := by
    rw [show ((13721978413 / 10000000000) : ℝ) = ((10000000000 / 13721978413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_937_neg : (9114403 / 62500000) ≤ -Real.log (1000 / 1157) ∧
    -Real.log (1000 / 1157) ≤ (145830449 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 2157)) (n := 12)
    (lo := (9114403 / 62500000)) (hi := (145830449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157 / 1000) = 1/(1000 / 1157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_937 : Bounds (9114403 / 62500000) (145830449 / 1000000000) (Real.log (1157 / 1000)) := by
  have h := reflection_log_937_neg
  have he : Real.log (1157 / 1000) = -Real.log (1000 / 1157) := by
    rw [show ((1157 / 1000) : ℝ) = ((1000 / 1157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_938_neg : (1067427 / 6250000) ≤ -Real.log (843 / 1000) ∧
    -Real.log (843 / 1000) ≤ (170788321 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 1843)) (n := 12)
    (lo := (1067427 / 6250000)) (hi := (170788321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 843) = 1/(843 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_938 : Bounds (-170788321 / 1000000000) (-1067427 / 6250000) (Real.log (843 / 1000)) := by
  have h := reflection_log_938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_939_neg : (156987 / 1000000000) ≤ -Real.log (1000000 / 1000157) ∧
    -Real.log (1000000 / 1000157) ≤ (39247 / 250000000) := by
  have h := checkLog_sound (w := (157 / 2000157)) (n := 12)
    (lo := (156987 / 1000000000)) (hi := (39247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000157 / 1000000) = 1/(1000000 / 1000157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_939 : Bounds (156987 / 1000000000) (39247 / 250000000) (Real.log (1000157 / 1000000)) := by
  have h := reflection_log_939_neg
  have he : Real.log (1000157 / 1000000) = -Real.log (1000000 / 1000157) := by
    rw [show ((1000157 / 1000000) : ℝ) = ((1000000 / 1000157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_940_neg : (39253 / 250000000) ≤ -Real.log (999843 / 1000000) ∧
    -Real.log (999843 / 1000000) ≤ (157013 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 1999843)) (n := 12)
    (lo := (39253 / 250000000)) (hi := (157013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999843) = 1/(999843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_940 : Bounds (-157013 / 1000000000) (-39253 / 250000000) (Real.log (999843 / 1000000)) := by
  have h := reflection_log_940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_941_neg : (75777007 / 1000000000) ≤ -Real.log (500000 / 539361) ∧
    -Real.log (500000 / 539361) ≤ (4736063 / 62500000) := by
  have h := checkLog_sound (w := (39361 / 1039361)) (n := 12)
    (lo := (75777007 / 1000000000)) (hi := (4736063 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539361 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539361 / 500000) = 1/(500000 / 539361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_941 : Bounds (75777007 / 1000000000) (4736063 / 62500000) (Real.log (539361 / 500000)) := by
  have h := reflection_log_941_neg
  have he : Real.log (539361 / 500000) = -Real.log (500000 / 539361) := by
    rw [show ((539361 / 500000) : ℝ) = ((500000 / 539361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_942_neg : (40996721 / 500000000) ≤ -Real.log (460639 / 500000) ∧
    -Real.log (460639 / 500000) ≤ (81993443 / 1000000000) := by
  have h := checkLog_sound (w := (39361 / 960639)) (n := 12)
    (lo := (40996721 / 500000000)) (hi := (81993443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460639) = 1/(460639 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_942 : Bounds (-81993443 / 1000000000) (-40996721 / 500000000) (Real.log (460639 / 500000)) := by
  have h := reflection_log_942_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_943_neg : (75969809 / 1000000000) ≤ -Real.log (100000 / 107893) ∧
    -Real.log (100000 / 107893) ≤ (7596981 / 100000000) := by
  have h := checkLog_sound (w := (7893 / 207893)) (n := 12)
    (lo := (75969809 / 1000000000)) (hi := (7596981 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107893 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107893 / 100000) = 1/(100000 / 107893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_943 : Bounds (75969809 / 1000000000) (7596981 / 100000000) (Real.log (107893 / 100000)) := by
  have h := reflection_log_943_neg
  have he : Real.log (107893 / 100000) = -Real.log (100000 / 107893) := by
    rw [show ((107893 / 100000) : ℝ) = ((100000 / 107893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_944_neg : (82219241 / 1000000000) ≤ -Real.log (92107 / 100000) ∧
    -Real.log (92107 / 100000) ≤ (41109621 / 500000000) := by
  have h := checkLog_sound (w := (7893 / 192107)) (n := 12)
    (lo := (82219241 / 1000000000)) (hi := (41109621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 92107) = 1/(92107 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_944 : Bounds (-41109621 / 500000000) (-82219241 / 1000000000) (Real.log (92107 / 100000)) := by
  have h := reflection_log_944_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_945_neg : (6249431 / 1000000000) ≤ -Real.log (9937700551 / 10000000000) ∧
    -Real.log (9937700551 / 10000000000) ≤ (781179 / 125000000) := by
  have h := checkLog_sound (w := (62299449 / 19937700551)) (n := 12)
    (lo := (6249431 / 1000000000)) (hi := (781179 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9937700551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9937700551) = 1/(9937700551 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_945 : Bounds (-781179 / 125000000) (-6249431 / 1000000000) (Real.log (9937700551 / 10000000000)) := by
  have h := reflection_log_945_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_946_neg : (1243287 / 200000000) ≤ -Real.log (248450711679 / 250000000000) ∧
    -Real.log (248450711679 / 250000000000) ≤ (1554109 / 250000000) := by
  have h := checkLog_sound (w := (1549288321 / 498450711679)) (n := 12)
    (lo := (1243287 / 200000000)) (hi := (1554109 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248450711679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248450711679) = 1/(248450711679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_946 : Bounds (-1554109 / 250000000) (-1243287 / 200000000) (Real.log (248450711679 / 250000000000)) := by
  have h := reflection_log_946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_947_neg : (157770449 / 1000000000) ≤ -Real.log (20000000000 / 23417947677) ∧
    -Real.log (20000000000 / 23417947677) ≤ (3155409 / 20000000) := by
  have h := checkLog_sound (w := (3417947677 / 43417947677)) (n := 12)
    (lo := (157770449 / 1000000000)) (hi := (3155409 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23417947677 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23417947677 / 20000000000) = 1/(20000000000 / 23417947677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_947 : Bounds (157770449 / 1000000000) (3155409 / 20000000) (Real.log (23417947677 / 20000000000)) := by
  have h := reflection_log_947_neg
  have he : Real.log (23417947677 / 20000000000) = -Real.log (20000000000 / 23417947677) := by
    rw [show ((23417947677 / 20000000000) : ℝ) = ((20000000000 / 23417947677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_948_neg : (3163781 / 20000000) ≤ -Real.log (500000000000 / 585693812631) ∧
    -Real.log (500000000000 / 585693812631) ≤ (158189051 / 1000000000) := by
  have h := checkLog_sound (w := (85693812631 / 1085693812631)) (n := 12)
    (lo := (3163781 / 20000000)) (hi := (158189051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585693812631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585693812631 / 500000000000) = 1/(500000000000 / 585693812631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_948 : Bounds (3163781 / 20000000) (158189051 / 1000000000) (Real.log (585693812631 / 500000000000)) := by
  have h := reflection_log_948_neg
  have he : Real.log (585693812631 / 500000000000) = -Real.log (500000000000 / 585693812631) := by
    rw [show ((585693812631 / 500000000000) : ℝ) = ((500000000000 / 585693812631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_949_neg : (158206859 / 500000000) ≤ -Real.log (500000000000 / 686098920649) ∧
    -Real.log (500000000000 / 686098920649) ≤ (316413719 / 1000000000) := by
  have h := checkLog_sound (w := (186098920649 / 1186098920649)) (n := 12)
    (lo := (158206859 / 500000000)) (hi := (316413719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((686098920649 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(686098920649 / 500000000000) = 1/(500000000000 / 686098920649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_949 : Bounds (158206859 / 500000000) (316413719 / 1000000000) (Real.log (686098920649 / 500000000000)) := by
  have h := reflection_log_949_neg
  have he : Real.log (686098920649 / 500000000000) = -Real.log (500000000000 / 686098920649) := by
    rw [show ((686098920649 / 500000000000) : ℝ) = ((500000000000 / 686098920649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_950_neg : (316618769 / 1000000000) ≤ -Real.log (125000000000 / 171559905101) ∧
    -Real.log (125000000000 / 171559905101) ≤ (31661877 / 100000000) := by
  have h := checkLog_sound (w := (46559905101 / 296559905101)) (n := 12)
    (lo := (316618769 / 1000000000)) (hi := (31661877 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171559905101 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171559905101 / 125000000000) = 1/(125000000000 / 171559905101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_950 : Bounds (316618769 / 1000000000) (31661877 / 100000000) (Real.log (171559905101 / 125000000000)) := by
  have h := reflection_log_950_neg
  have he : Real.log (171559905101 / 125000000000) = -Real.log (125000000000 / 171559905101) := by
    rw [show ((171559905101 / 125000000000) : ℝ) = ((125000000000 / 171559905101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_951_neg : (72958437 / 500000000) ≤ -Real.log (10000 / 11571) ∧
    -Real.log (10000 / 11571) ≤ (233467 / 1600000) := by
  have h := checkLog_sound (w := (1571 / 21571)) (n := 12)
    (lo := (72958437 / 500000000)) (hi := (233467 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11571 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11571 / 10000) = 1/(10000 / 11571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_951 : Bounds (72958437 / 500000000) (233467 / 1600000) (Real.log (11571 / 10000)) := by
  have h := reflection_log_951_neg
  have he : Real.log (11571 / 10000) = -Real.log (10000 / 11571) := by
    rw [show ((11571 / 10000) : ℝ) = ((10000 / 11571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_952_neg : (170906951 / 1000000000) ≤ -Real.log (8429 / 10000) ∧
    -Real.log (8429 / 10000) ≤ (21363369 / 125000000) := by
  have h := checkLog_sound (w := (1571 / 18429)) (n := 12)
    (lo := (170906951 / 1000000000)) (hi := (21363369 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8429) = 1/(8429 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_952 : Bounds (-21363369 / 125000000) (-170906951 / 1000000000) (Real.log (8429 / 10000)) := by
  have h := reflection_log_952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_953_neg : (157087 / 1000000000) ≤ -Real.log (10000000 / 10001571) ∧
    -Real.log (10000000 / 10001571) ≤ (4909 / 31250000) := by
  have h := checkLog_sound (w := (1571 / 20001571)) (n := 12)
    (lo := (157087 / 1000000000)) (hi := (4909 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001571 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001571 / 10000000) = 1/(10000000 / 10001571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_953 : Bounds (157087 / 1000000000) (4909 / 31250000) (Real.log (10001571 / 10000000)) := by
  have h := reflection_log_953_neg
  have he : Real.log (10001571 / 10000000) = -Real.log (10000000 / 10001571) := by
    rw [show ((10001571 / 10000000) : ℝ) = ((10000000 / 10001571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_954_neg : (19639 / 125000000) ≤ -Real.log (9998429 / 10000000) ∧
    -Real.log (9998429 / 10000000) ≤ (157113 / 1000000000) := by
  have h := checkLog_sound (w := (1571 / 19998429)) (n := 12)
    (lo := (19639 / 125000000)) (hi := (157113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998429) = 1/(9998429 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_954 : Bounds (-157113 / 1000000000) (-19639 / 125000000) (Real.log (9998429 / 10000000)) := by
  have h := reflection_log_954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_955_neg : (18956071 / 250000000) ≤ -Real.log (1000000 / 1078773) ∧
    -Real.log (1000000 / 1078773) ≤ (15164857 / 200000000) := by
  have h := checkLog_sound (w := (78773 / 2078773)) (n := 12)
    (lo := (18956071 / 250000000)) (hi := (15164857 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078773 / 1000000) = 1/(1000000 / 1078773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_955 : Bounds (18956071 / 250000000) (15164857 / 200000000) (Real.log (1078773 / 1000000)) := by
  have h := reflection_log_955_neg
  have he : Real.log (1078773 / 1000000) = -Real.log (1000000 / 1078773) := by
    rw [show ((1078773 / 1000000) : ℝ) = ((1000000 / 1078773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_956_neg : (82048801 / 1000000000) ≤ -Real.log (921227 / 1000000) ∧
    -Real.log (921227 / 1000000) ≤ (41024401 / 500000000) := by
  have h := checkLog_sound (w := (78773 / 1921227)) (n := 12)
    (lo := (82048801 / 1000000000)) (hi := (41024401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921227) = 1/(921227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_956 : Bounds (-41024401 / 500000000) (-82048801 / 1000000000) (Real.log (921227 / 1000000)) := by
  have h := reflection_log_956_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_957_neg : (76017077 / 1000000000) ≤ -Real.log (1000000 / 1078981) ∧
    -Real.log (1000000 / 1078981) ≤ (38008539 / 500000000) := by
  have h := checkLog_sound (w := (78981 / 2078981)) (n := 12)
    (lo := (76017077 / 1000000000)) (hi := (38008539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078981 / 1000000) = 1/(1000000 / 1078981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_957 : Bounds (76017077 / 1000000000) (38008539 / 500000000) (Real.log (1078981 / 1000000)) := by
  have h := reflection_log_957_neg
  have he : Real.log (1078981 / 1000000) = -Real.log (1000000 / 1078981) := by
    rw [show ((1078981 / 1000000) : ℝ) = ((1000000 / 1078981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_958_neg : (82274613 / 1000000000) ≤ -Real.log (921019 / 1000000) ∧
    -Real.log (921019 / 1000000) ≤ (41137307 / 500000000) := by
  have h := checkLog_sound (w := (78981 / 1921019)) (n := 12)
    (lo := (82274613 / 1000000000)) (hi := (41137307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921019) = 1/(921019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_958 : Bounds (-41137307 / 500000000) (-82274613 / 1000000000) (Real.log (921019 / 1000000)) := by
  have h := reflection_log_958_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_959_neg : (1251507 / 200000000) ≤ -Real.log (993762001639 / 1000000000000) ∧
    -Real.log (993762001639 / 1000000000000) ≤ (48887 / 7812500) := by
  have h := checkLog_sound (w := (6237998361 / 1993762001639)) (n := 12)
    (lo := (1251507 / 200000000)) (hi := (48887 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993762001639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993762001639) = 1/(993762001639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_959 : Bounds (-48887 / 7812500) (-1251507 / 200000000) (Real.log (993762001639 / 1000000000000)) := by
  have h := reflection_log_959_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
