import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3968_neg : (18841917 / 200000000) ≤ -Real.log (227523 / 250000) ∧
    -Real.log (227523 / 250000) ≤ (47104793 / 500000000) := by
  have h := checkLog_sound (w := (22477 / 477523)) (n := 12)
    (lo := (18841917 / 200000000)) (hi := (47104793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227523) = 1/(227523 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3968 : Bounds (-47104793 / 500000000) (-18841917 / 200000000) (Real.log (227523 / 250000)) := by
  have h := reflection_log_3968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3969_neg : (1014537 / 125000000) ≤ -Real.log (61994784471 / 62500000000) ∧
    -Real.log (61994784471 / 62500000000) ≤ (8116297 / 1000000000) := by
  have h := checkLog_sound (w := (505215529 / 124494784471)) (n := 12)
    (lo := (1014537 / 125000000)) (hi := (8116297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61994784471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61994784471) = 1/(61994784471 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3969 : Bounds (-8116297 / 1000000000) (-1014537 / 125000000) (Real.log (61994784471 / 62500000000)) := by
  have h := reflection_log_3969_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3970_neg : (252333 / 31250000) ≤ -Real.log (247989464079 / 250000000000) ∧
    -Real.log (247989464079 / 250000000000) ≤ (8074657 / 1000000000) := by
  have h := checkLog_sound (w := (2010535921 / 497989464079)) (n := 12)
    (lo := (252333 / 31250000)) (hi := (8074657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247989464079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247989464079) = 1/(247989464079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3970 : Bounds (-8074657 / 1000000000) (-252333 / 31250000) (Real.log (247989464079 / 250000000000)) := by
  have h := reflection_log_3970_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3971_neg : (35967827 / 200000000) ≤ -Real.log (100000000000 / 119702478903) ∧
    -Real.log (100000000000 / 119702478903) ≤ (5619973 / 31250000) := by
  have h := checkLog_sound (w := (19702478903 / 219702478903)) (n := 12)
    (lo := (35967827 / 200000000)) (hi := (5619973 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119702478903 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119702478903 / 100000000000) = 1/(100000000000 / 119702478903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3971 : Bounds (35967827 / 200000000) (5619973 / 31250000) (Real.log (119702478903 / 100000000000)) := by
  have h := reflection_log_3971_neg
  have he : Real.log (119702478903 / 100000000000) = -Real.log (100000000000 / 119702478903) := by
    rw [show ((119702478903 / 100000000000) : ℝ) = ((100000000000 / 119702478903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3972_neg : (90151437 / 500000000) ≤ -Real.log (500000000000 / 598790012439) ∧
    -Real.log (500000000000 / 598790012439) ≤ (1442423 / 8000000) := by
  have h := checkLog_sound (w := (98790012439 / 1098790012439)) (n := 12)
    (lo := (90151437 / 500000000)) (hi := (1442423 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598790012439 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598790012439 / 500000000000) = 1/(500000000000 / 598790012439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3972 : Bounds (90151437 / 500000000) (1442423 / 8000000) (Real.log (598790012439 / 500000000000)) := by
  have h := reflection_log_3972_neg
  have he : Real.log (598790012439 / 500000000000) = -Real.log (500000000000 / 598790012439) := by
    rw [show ((598790012439 / 500000000000) : ℝ) = ((500000000000 / 598790012439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3973_neg : (45108223 / 125000000) ≤ -Real.log (250000000000 / 358642726719) ∧
    -Real.log (250000000000 / 358642726719) ≤ (72173157 / 200000000) := by
  have h := checkLog_sound (w := (108642726719 / 608642726719)) (n := 12)
    (lo := (45108223 / 125000000)) (hi := (72173157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358642726719 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358642726719 / 250000000000) = 1/(250000000000 / 358642726719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3973 : Bounds (45108223 / 125000000) (72173157 / 200000000) (Real.log (358642726719 / 250000000000)) := by
  have h := reflection_log_3973_neg
  have he : Real.log (358642726719 / 250000000000) = -Real.log (250000000000 / 358642726719) := by
    rw [show ((358642726719 / 250000000000) : ℝ) = ((250000000000 / 358642726719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3974_neg : (36107237 / 100000000) ≤ -Real.log (500000000000 / 717433649867) ∧
    -Real.log (500000000000 / 717433649867) ≤ (361072371 / 1000000000) := by
  have h := checkLog_sound (w := (217433649867 / 1217433649867)) (n := 12)
    (lo := (36107237 / 100000000)) (hi := (361072371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717433649867 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717433649867 / 500000000000) = 1/(500000000000 / 717433649867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3974 : Bounds (36107237 / 100000000) (361072371 / 1000000000) (Real.log (717433649867 / 500000000000)) := by
  have h := reflection_log_3974_neg
  have he : Real.log (717433649867 / 500000000000) = -Real.log (500000000000 / 717433649867) := by
    rw [show ((717433649867 / 500000000000) : ℝ) = ((500000000000 / 717433649867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3975_neg : (20551517 / 125000000) ≤ -Real.log (10000 / 11787) ∧
    -Real.log (10000 / 11787) ≤ (164412137 / 1000000000) := by
  have h := checkLog_sound (w := (1787 / 21787)) (n := 12)
    (lo := (20551517 / 125000000)) (hi := (164412137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11787 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11787 / 10000) = 1/(10000 / 11787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3975 : Bounds (20551517 / 125000000) (164412137 / 1000000000) (Real.log (11787 / 10000)) := by
  have h := reflection_log_3975_neg
  have he : Real.log (11787 / 10000) = -Real.log (10000 / 11787) := by
    rw [show ((11787 / 10000) : ℝ) = ((10000 / 11787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3976_neg : (49216707 / 250000000) ≤ -Real.log (8213 / 10000) ∧
    -Real.log (8213 / 10000) ≤ (196866829 / 1000000000) := by
  have h := checkLog_sound (w := (1787 / 18213)) (n := 12)
    (lo := (49216707 / 250000000)) (hi := (196866829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8213) = 1/(8213 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3976 : Bounds (-196866829 / 1000000000) (-49216707 / 250000000) (Real.log (8213 / 10000)) := by
  have h := reflection_log_3976_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3977_neg : (44671 / 250000000) ≤ -Real.log (10000000 / 10001787) ∧
    -Real.log (10000000 / 10001787) ≤ (35737 / 200000000) := by
  have h := checkLog_sound (w := (1787 / 20001787)) (n := 12)
    (lo := (44671 / 250000000)) (hi := (35737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001787 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001787 / 10000000) = 1/(10000000 / 10001787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3977 : Bounds (44671 / 250000000) (35737 / 200000000) (Real.log (10001787 / 10000000)) := by
  have h := reflection_log_3977_neg
  have he : Real.log (10001787 / 10000000) = -Real.log (10000000 / 10001787) := by
    rw [show ((10001787 / 10000000) : ℝ) = ((10000000 / 10001787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3978_neg : (35743 / 200000000) ≤ -Real.log (9998213 / 10000000) ∧
    -Real.log (9998213 / 10000000) ≤ (44679 / 250000000) := by
  have h := checkLog_sound (w := (1787 / 19998213)) (n := 12)
    (lo := (35743 / 200000000)) (hi := (44679 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998213) = 1/(9998213 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3978 : Bounds (-44679 / 250000000) (-35743 / 200000000) (Real.log (9998213 / 10000000)) := by
  have h := reflection_log_3978_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3979_neg : (85929041 / 1000000000) ≤ -Real.log (1000000 / 1089729) ∧
    -Real.log (1000000 / 1089729) ≤ (42964521 / 500000000) := by
  have h := checkLog_sound (w := (89729 / 2089729)) (n := 12)
    (lo := (85929041 / 1000000000)) (hi := (42964521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089729 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089729 / 1000000) = 1/(1000000 / 1089729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3979 : Bounds (85929041 / 1000000000) (42964521 / 500000000) (Real.log (1089729 / 1000000)) := by
  have h := reflection_log_3979_neg
  have he : Real.log (1089729 / 1000000) = -Real.log (1000000 / 1089729) := by
    rw [show ((1089729 / 1000000) : ℝ) = ((1000000 / 1089729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3980_neg : (94012921 / 1000000000) ≤ -Real.log (910271 / 1000000) ∧
    -Real.log (910271 / 1000000) ≤ (47006461 / 500000000) := by
  have h := checkLog_sound (w := (89729 / 1910271)) (n := 12)
    (lo := (94012921 / 1000000000)) (hi := (47006461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910271) = 1/(910271 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3980 : Bounds (-47006461 / 500000000) (-94012921 / 1000000000) (Real.log (910271 / 1000000)) := by
  have h := reflection_log_3980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3981_neg : (1076751 / 12500000) ≤ -Real.log (1000000 / 1089959) ∧
    -Real.log (1000000 / 1089959) ≤ (86140081 / 1000000000) := by
  have h := checkLog_sound (w := (89959 / 2089959)) (n := 12)
    (lo := (1076751 / 12500000)) (hi := (86140081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089959 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089959 / 1000000) = 1/(1000000 / 1089959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3981 : Bounds (1076751 / 12500000) (86140081 / 1000000000) (Real.log (1089959 / 1000000)) := by
  have h := reflection_log_3981_neg
  have he : Real.log (1089959 / 1000000) = -Real.log (1000000 / 1089959) := by
    rw [show ((1089959 / 1000000) : ℝ) = ((1000000 / 1089959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3982_neg : (6033 / 64000) ≤ -Real.log (910041 / 1000000) ∧
    -Real.log (910041 / 1000000) ≤ (47132813 / 500000000) := by
  have h := checkLog_sound (w := (89959 / 1910041)) (n := 12)
    (lo := (6033 / 64000)) (hi := (47132813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910041) = 1/(910041 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3982 : Bounds (-47132813 / 500000000) (-6033 / 64000) (Real.log (910041 / 1000000)) := by
  have h := reflection_log_3982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3983_neg : (1015693 / 125000000) ≤ -Real.log (991907378319 / 1000000000000) ∧
    -Real.log (991907378319 / 1000000000000) ≤ (1625109 / 200000000) := by
  have h := checkLog_sound (w := (8092621681 / 1991907378319)) (n := 12)
    (lo := (1015693 / 125000000)) (hi := (1625109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991907378319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991907378319) = 1/(991907378319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3983 : Bounds (-1625109 / 200000000) (-1015693 / 125000000) (Real.log (991907378319 / 1000000000000)) := by
  have h := reflection_log_3983_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3984_neg : (202097 / 25000000) ≤ -Real.log (991948706559 / 1000000000000) ∧
    -Real.log (991948706559 / 1000000000000) ≤ (8083881 / 1000000000) := by
  have h := checkLog_sound (w := (8051293441 / 1991948706559)) (n := 12)
    (lo := (202097 / 25000000)) (hi := (8083881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991948706559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991948706559) = 1/(991948706559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3984 : Bounds (-8083881 / 1000000000) (-202097 / 25000000) (Real.log (991948706559 / 1000000000000)) := by
  have h := reflection_log_3984_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3985_neg : (179941963 / 1000000000) ≤ -Real.log (250000000000 / 299286970583) ∧
    -Real.log (250000000000 / 299286970583) ≤ (44985491 / 250000000) := by
  have h := checkLog_sound (w := (49286970583 / 549286970583)) (n := 12)
    (lo := (179941963 / 1000000000)) (hi := (44985491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299286970583 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299286970583 / 250000000000) = 1/(250000000000 / 299286970583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3985 : Bounds (179941963 / 1000000000) (44985491 / 250000000) (Real.log (299286970583 / 250000000000)) := by
  have h := reflection_log_3985_neg
  have he : Real.log (299286970583 / 250000000000) = -Real.log (250000000000 / 299286970583) := by
    rw [show ((299286970583 / 250000000000) : ℝ) = ((250000000000 / 299286970583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3986_neg : (90202853 / 500000000) ≤ -Real.log (125000000000 / 149712897551) ∧
    -Real.log (125000000000 / 149712897551) ≤ (180405707 / 1000000000) := by
  have h := checkLog_sound (w := (24712897551 / 274712897551)) (n := 12)
    (lo := (90202853 / 500000000)) (hi := (180405707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149712897551 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149712897551 / 125000000000) = 1/(125000000000 / 149712897551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3986 : Bounds (90202853 / 500000000) (180405707 / 1000000000) (Real.log (149712897551 / 125000000000)) := by
  have h := reflection_log_3986_neg
  have he : Real.log (149712897551 / 125000000000) = -Real.log (125000000000 / 149712897551) := by
    rw [show ((149712897551 / 125000000000) : ℝ) = ((125000000000 / 149712897551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3987_neg : (36107237 / 100000000) ≤ -Real.log (250000000000 / 358716824933) ∧
    -Real.log (250000000000 / 358716824933) ≤ (361072371 / 1000000000) := by
  have h := checkLog_sound (w := (108716824933 / 608716824933)) (n := 12)
    (lo := (36107237 / 100000000)) (hi := (361072371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358716824933 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358716824933 / 250000000000) = 1/(250000000000 / 358716824933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3987 : Bounds (36107237 / 100000000) (361072371 / 1000000000) (Real.log (358716824933 / 250000000000)) := by
  have h := reflection_log_3987_neg
  have he : Real.log (358716824933 / 250000000000) = -Real.log (250000000000 / 358716824933) := by
    rw [show ((358716824933 / 250000000000) : ℝ) = ((250000000000 / 358716824933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3988_neg : (90319741 / 250000000) ≤ -Real.log (250000000000 / 358790941191) ∧
    -Real.log (250000000000 / 358790941191) ≤ (72255793 / 200000000) := by
  have h := checkLog_sound (w := (108790941191 / 608790941191)) (n := 12)
    (lo := (90319741 / 250000000)) (hi := (72255793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358790941191 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358790941191 / 250000000000) = 1/(250000000000 / 358790941191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3988 : Bounds (90319741 / 250000000) (72255793 / 200000000) (Real.log (358790941191 / 250000000000)) := by
  have h := reflection_log_3988_neg
  have he : Real.log (358790941191 / 250000000000) = -Real.log (250000000000 / 358790941191) := by
    rw [show ((358790941191 / 250000000000) : ℝ) = ((250000000000 / 358790941191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3989_neg : (164496971 / 1000000000) ≤ -Real.log (2500 / 2947) ∧
    -Real.log (2500 / 2947) ≤ (41124243 / 250000000) := by
  have h := checkLog_sound (w := (447 / 5447)) (n := 12)
    (lo := (164496971 / 1000000000)) (hi := (41124243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2947 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2947 / 2500) = 1/(2500 / 2947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3989 : Bounds (164496971 / 1000000000) (41124243 / 250000000) (Real.log (2947 / 2500)) := by
  have h := reflection_log_3989_neg
  have he : Real.log (2947 / 2500) = -Real.log (2500 / 2947) := by
    rw [show ((2947 / 2500) : ℝ) = ((2500 / 2947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3990_neg : (196988593 / 1000000000) ≤ -Real.log (2053 / 2500) ∧
    -Real.log (2053 / 2500) ≤ (98494297 / 500000000) := by
  have h := checkLog_sound (w := (447 / 4553)) (n := 12)
    (lo := (196988593 / 1000000000)) (hi := (98494297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2053) = 1/(2053 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3990 : Bounds (-98494297 / 500000000) (-196988593 / 1000000000) (Real.log (2053 / 2500)) := by
  have h := reflection_log_3990_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3991_neg : (5587 / 31250000) ≤ -Real.log (2500000 / 2500447) ∧
    -Real.log (2500000 / 2500447) ≤ (35757 / 200000000) := by
  have h := checkLog_sound (w := (447 / 5000447)) (n := 12)
    (lo := (5587 / 31250000)) (hi := (35757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500447 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500447 / 2500000) = 1/(2500000 / 2500447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3991 : Bounds (5587 / 31250000) (35757 / 200000000) (Real.log (2500447 / 2500000)) := by
  have h := reflection_log_3991_neg
  have he : Real.log (2500447 / 2500000) = -Real.log (2500000 / 2500447) := by
    rw [show ((2500447 / 2500000) : ℝ) = ((2500000 / 2500447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3992_neg : (35763 / 200000000) ≤ -Real.log (2499553 / 2500000) ∧
    -Real.log (2499553 / 2500000) ≤ (1397 / 7812500) := by
  have h := checkLog_sound (w := (447 / 4999553)) (n := 12)
    (lo := (35763 / 200000000)) (hi := (1397 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499553) = 1/(2499553 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3992 : Bounds (-1397 / 7812500) (-35763 / 200000000) (Real.log (2499553 / 2500000)) := by
  have h := reflection_log_3992_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3993_neg : (85975841 / 1000000000) ≤ -Real.log (50000 / 54489) ∧
    -Real.log (50000 / 54489) ≤ (42987921 / 500000000) := by
  have h := checkLog_sound (w := (4489 / 104489)) (n := 12)
    (lo := (85975841 / 1000000000)) (hi := (42987921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54489 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54489 / 50000) = 1/(50000 / 54489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3993 : Bounds (85975841 / 1000000000) (42987921 / 500000000) (Real.log (54489 / 50000)) := by
  have h := reflection_log_3993_neg
  have he : Real.log (54489 / 50000) = -Real.log (50000 / 54489) := by
    rw [show ((54489 / 50000) : ℝ) = ((50000 / 54489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3994_neg : (1881379 / 20000000) ≤ -Real.log (45511 / 50000) ∧
    -Real.log (45511 / 50000) ≤ (94068951 / 1000000000) := by
  have h := checkLog_sound (w := (4489 / 95511)) (n := 12)
    (lo := (1881379 / 20000000)) (hi := (94068951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45511) = 1/(45511 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3994 : Bounds (-94068951 / 1000000000) (-1881379 / 20000000) (Real.log (45511 / 50000)) := by
  have h := reflection_log_3994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3995_neg : (8618687 / 100000000) ≤ -Real.log (100000 / 109001) ∧
    -Real.log (100000 / 109001) ≤ (86186871 / 1000000000) := by
  have h := checkLog_sound (w := (9001 / 209001)) (n := 12)
    (lo := (8618687 / 100000000)) (hi := (86186871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109001 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109001 / 100000) = 1/(100000 / 109001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3995 : Bounds (8618687 / 100000000) (86186871 / 1000000000) (Real.log (109001 / 100000)) := by
  have h := reflection_log_3995_neg
  have he : Real.log (109001 / 100000) = -Real.log (100000 / 109001) := by
    rw [show ((109001 / 100000) : ℝ) = ((100000 / 109001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3996_neg : (23580417 / 250000000) ≤ -Real.log (90999 / 100000) ∧
    -Real.log (90999 / 100000) ≤ (94321669 / 1000000000) := by
  have h := checkLog_sound (w := (9001 / 190999)) (n := 12)
    (lo := (23580417 / 250000000)) (hi := (94321669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90999) = 1/(90999 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3996 : Bounds (-94321669 / 1000000000) (-23580417 / 250000000) (Real.log (90999 / 100000)) := by
  have h := reflection_log_3996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3997_neg : (4067399 / 500000000) ≤ -Real.log (9918981999 / 10000000000) ∧
    -Real.log (9918981999 / 10000000000) ≤ (8134799 / 1000000000) := by
  have h := checkLog_sound (w := (81018001 / 19918981999)) (n := 12)
    (lo := (4067399 / 500000000)) (hi := (8134799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9918981999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9918981999) = 1/(9918981999 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3997 : Bounds (-8134799 / 1000000000) (-4067399 / 500000000) (Real.log (9918981999 / 10000000000)) := by
  have h := reflection_log_3997_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3998_neg : (8093109 / 1000000000) ≤ -Real.log (2479848879 / 2500000000) ∧
    -Real.log (2479848879 / 2500000000) ≤ (809311 / 100000000) := by
  have h := checkLog_sound (w := (20151121 / 4979848879)) (n := 12)
    (lo := (8093109 / 1000000000)) (hi := (809311 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2479848879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2479848879) = 1/(2479848879 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3998 : Bounds (-809311 / 100000000) (-8093109 / 1000000000) (Real.log (2479848879 / 2500000000)) := by
  have h := reflection_log_3998_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3999_neg : (180044791 / 1000000000) ≤ -Real.log (100000000000 / 119727098943) ∧
    -Real.log (100000000000 / 119727098943) ≤ (22505599 / 125000000) := by
  have h := checkLog_sound (w := (19727098943 / 219727098943)) (n := 12)
    (lo := (180044791 / 1000000000)) (hi := (22505599 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119727098943 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119727098943 / 100000000000) = 1/(100000000000 / 119727098943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3999 : Bounds (180044791 / 1000000000) (22505599 / 125000000) (Real.log (119727098943 / 100000000000)) := by
  have h := reflection_log_3999_neg
  have he : Real.log (119727098943 / 100000000000) = -Real.log (100000000000 / 119727098943) := by
    rw [show ((119727098943 / 100000000000) : ℝ) = ((100000000000 / 119727098943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4000_neg : (180508539 / 1000000000) ≤ -Real.log (500000000000 / 598913174871) ∧
    -Real.log (500000000000 / 598913174871) ≤ (9025427 / 50000000) := by
  have h := checkLog_sound (w := (98913174871 / 1098913174871)) (n := 12)
    (lo := (180508539 / 1000000000)) (hi := (9025427 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598913174871 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598913174871 / 500000000000) = 1/(500000000000 / 598913174871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4000 : Bounds (180508539 / 1000000000) (9025427 / 50000000) (Real.log (598913174871 / 500000000000)) := by
  have h := reflection_log_4000_neg
  have he : Real.log (598913174871 / 500000000000) = -Real.log (500000000000 / 598913174871) := by
    rw [show ((598913174871 / 500000000000) : ℝ) = ((500000000000 / 598913174871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4001_neg : (90319741 / 250000000) ≤ -Real.log (500000000000 / 717581882381) ∧
    -Real.log (500000000000 / 717581882381) ≤ (72255793 / 200000000) := by
  have h := checkLog_sound (w := (217581882381 / 1217581882381)) (n := 12)
    (lo := (90319741 / 250000000)) (hi := (72255793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717581882381 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717581882381 / 500000000000) = 1/(500000000000 / 717581882381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4001 : Bounds (90319741 / 250000000) (72255793 / 200000000) (Real.log (717581882381 / 500000000000)) := by
  have h := reflection_log_4001_neg
  have he : Real.log (717581882381 / 500000000000) = -Real.log (500000000000 / 717581882381) := by
    rw [show ((717581882381 / 500000000000) : ℝ) = ((500000000000 / 717581882381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4002_neg : (72297113 / 200000000) ≤ -Real.log (500000000000 / 717730150999) ∧
    -Real.log (500000000000 / 717730150999) ≤ (180742783 / 500000000) := by
  have h := checkLog_sound (w := (217730150999 / 1217730150999)) (n := 12)
    (lo := (72297113 / 200000000)) (hi := (180742783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717730150999 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717730150999 / 500000000000) = 1/(500000000000 / 717730150999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4002 : Bounds (72297113 / 200000000) (180742783 / 500000000) (Real.log (717730150999 / 500000000000)) := by
  have h := reflection_log_4002_neg
  have he : Real.log (717730150999 / 500000000000) = -Real.log (500000000000 / 717730150999) := by
    rw [show ((717730150999 / 500000000000) : ℝ) = ((500000000000 / 717730150999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4003_neg : (822909 / 5000000) ≤ -Real.log (10000 / 11789) ∧
    -Real.log (10000 / 11789) ≤ (164581801 / 1000000000) := by
  have h := checkLog_sound (w := (1789 / 21789)) (n := 12)
    (lo := (822909 / 5000000)) (hi := (164581801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11789 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11789 / 10000) = 1/(10000 / 11789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4003 : Bounds (822909 / 5000000) (164581801 / 1000000000) (Real.log (11789 / 10000)) := by
  have h := reflection_log_4003_neg
  have he : Real.log (11789 / 10000) = -Real.log (10000 / 11789) := by
    rw [show ((11789 / 10000) : ℝ) = ((10000 / 11789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4004_neg : (98555187 / 500000000) ≤ -Real.log (8211 / 10000) ∧
    -Real.log (8211 / 10000) ≤ (1576883 / 8000000) := by
  have h := checkLog_sound (w := (1789 / 18211)) (n := 12)
    (lo := (98555187 / 500000000)) (hi := (1576883 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8211) = 1/(8211 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4004 : Bounds (-1576883 / 8000000) (-98555187 / 500000000) (Real.log (8211 / 10000)) := by
  have h := reflection_log_4004_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4005_neg : (178883 / 1000000000) ≤ -Real.log (10000000 / 10001789) ∧
    -Real.log (10000000 / 10001789) ≤ (44721 / 250000000) := by
  have h := checkLog_sound (w := (1789 / 20001789)) (n := 12)
    (lo := (178883 / 1000000000)) (hi := (44721 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001789 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001789 / 10000000) = 1/(10000000 / 10001789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4005 : Bounds (178883 / 1000000000) (44721 / 250000000) (Real.log (10001789 / 10000000)) := by
  have h := reflection_log_4005_neg
  have he : Real.log (10001789 / 10000000) = -Real.log (10000000 / 10001789) := by
    rw [show ((10001789 / 10000000) : ℝ) = ((10000000 / 10001789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4006_neg : (44729 / 250000000) ≤ -Real.log (9998211 / 10000000) ∧
    -Real.log (9998211 / 10000000) ≤ (178917 / 1000000000) := by
  have h := checkLog_sound (w := (1789 / 19998211)) (n := 12)
    (lo := (44729 / 250000000)) (hi := (178917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998211) = 1/(9998211 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4006 : Bounds (-178917 / 1000000000) (-44729 / 250000000) (Real.log (9998211 / 10000000)) := by
  have h := reflection_log_4006_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4007_neg : (43011319 / 500000000) ≤ -Real.log (1000000 / 1089831) ∧
    -Real.log (1000000 / 1089831) ≤ (86022639 / 1000000000) := by
  have h := checkLog_sound (w := (89831 / 2089831)) (n := 12)
    (lo := (43011319 / 500000000)) (hi := (86022639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089831 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089831 / 1000000) = 1/(1000000 / 1089831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4007 : Bounds (43011319 / 500000000) (86022639 / 1000000000) (Real.log (1089831 / 1000000)) := by
  have h := reflection_log_4007_neg
  have he : Real.log (1089831 / 1000000) = -Real.log (1000000 / 1089831) := by
    rw [show ((1089831 / 1000000) : ℝ) = ((1000000 / 1089831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4008_neg : (47062491 / 500000000) ≤ -Real.log (910169 / 1000000) ∧
    -Real.log (910169 / 1000000) ≤ (94124983 / 1000000000) := by
  have h := checkLog_sound (w := (89831 / 1910169)) (n := 12)
    (lo := (47062491 / 500000000)) (hi := (94124983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910169) = 1/(910169 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4008 : Bounds (-94124983 / 1000000000) (-47062491 / 500000000) (Real.log (910169 / 1000000)) := by
  have h := reflection_log_4008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4009_neg : (86233657 / 1000000000) ≤ -Real.log (1000000 / 1090061) ∧
    -Real.log (1000000 / 1090061) ≤ (43116829 / 500000000) := by
  have h := checkLog_sound (w := (90061 / 2090061)) (n := 12)
    (lo := (86233657 / 1000000000)) (hi := (43116829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090061 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090061 / 1000000) = 1/(1000000 / 1090061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4009 : Bounds (86233657 / 1000000000) (43116829 / 500000000) (Real.log (1090061 / 1000000)) := by
  have h := reflection_log_4009_neg
  have he : Real.log (1090061 / 1000000) = -Real.log (1000000 / 1090061) := by
    rw [show ((1090061 / 1000000) : ℝ) = ((1000000 / 1090061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4010_neg : (47188857 / 500000000) ≤ -Real.log (909939 / 1000000) ∧
    -Real.log (909939 / 1000000) ≤ (18875543 / 200000000) := by
  have h := checkLog_sound (w := (90061 / 1909939)) (n := 12)
    (lo := (47188857 / 500000000)) (hi := (18875543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909939) = 1/(909939 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4010 : Bounds (-18875543 / 200000000) (-47188857 / 500000000) (Real.log (909939 / 1000000)) := by
  have h := reflection_log_4010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4011_neg : (1018007 / 125000000) ≤ -Real.log (991889016279 / 1000000000000) ∧
    -Real.log (991889016279 / 1000000000000) ≤ (8144057 / 1000000000) := by
  have h := checkLog_sound (w := (8110983721 / 1991889016279)) (n := 12)
    (lo := (1018007 / 125000000)) (hi := (8144057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991889016279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991889016279) = 1/(991889016279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4011 : Bounds (-8144057 / 1000000000) (-1018007 / 125000000) (Real.log (991889016279 / 1000000000000)) := by
  have h := reflection_log_4011_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4012_neg : (1012793 / 125000000) ≤ -Real.log (991930391439 / 1000000000000) ∧
    -Real.log (991930391439 / 1000000000000) ≤ (1620469 / 200000000) := by
  have h := checkLog_sound (w := (8069608561 / 1991930391439)) (n := 12)
    (lo := (1012793 / 125000000)) (hi := (1620469 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991930391439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991930391439) = 1/(991930391439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4012 : Bounds (-1620469 / 200000000) (-1012793 / 125000000) (Real.log (991930391439 / 1000000000000)) := by
  have h := reflection_log_4012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4013_neg : (9007381 / 50000000) ≤ -Real.log (250000000000 / 299348527581) ∧
    -Real.log (250000000000 / 299348527581) ≤ (180147621 / 1000000000) := by
  have h := checkLog_sound (w := (49348527581 / 549348527581)) (n := 12)
    (lo := (9007381 / 50000000)) (hi := (180147621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299348527581 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299348527581 / 250000000000) = 1/(250000000000 / 299348527581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4013 : Bounds (9007381 / 50000000) (180147621 / 1000000000) (Real.log (299348527581 / 250000000000)) := by
  have h := reflection_log_4013_neg
  have he : Real.log (299348527581 / 250000000000) = -Real.log (250000000000 / 299348527581) := by
    rw [show ((299348527581 / 250000000000) : ℝ) = ((250000000000 / 299348527581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4014_neg : (45152843 / 250000000) ≤ -Real.log (500000000000 / 598974766441) ∧
    -Real.log (500000000000 / 598974766441) ≤ (180611373 / 1000000000) := by
  have h := checkLog_sound (w := (98974766441 / 1098974766441)) (n := 12)
    (lo := (45152843 / 250000000)) (hi := (180611373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598974766441 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598974766441 / 500000000000) = 1/(500000000000 / 598974766441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4014 : Bounds (45152843 / 250000000) (180611373 / 1000000000) (Real.log (598974766441 / 500000000000)) := by
  have h := reflection_log_4014_neg
  have he : Real.log (598974766441 / 500000000000) = -Real.log (500000000000 / 598974766441) := by
    rw [show ((598974766441 / 500000000000) : ℝ) = ((500000000000 / 598974766441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4015_neg : (72297113 / 200000000) ≤ -Real.log (250000000000 / 358865075499) ∧
    -Real.log (250000000000 / 358865075499) ≤ (180742783 / 500000000) := by
  have h := checkLog_sound (w := (108865075499 / 608865075499)) (n := 12)
    (lo := (72297113 / 200000000)) (hi := (180742783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358865075499 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358865075499 / 250000000000) = 1/(250000000000 / 358865075499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4015 : Bounds (72297113 / 200000000) (180742783 / 500000000) (Real.log (358865075499 / 250000000000)) := by
  have h := reflection_log_4015_neg
  have he : Real.log (358865075499 / 250000000000) = -Real.log (250000000000 / 358865075499) := by
    rw [show ((358865075499 / 250000000000) : ℝ) = ((250000000000 / 358865075499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4016_neg : (180846087 / 500000000) ≤ -Real.log (500000000000 / 717878455731) ∧
    -Real.log (500000000000 / 717878455731) ≤ (14467687 / 40000000) := by
  have h := checkLog_sound (w := (217878455731 / 1217878455731)) (n := 12)
    (lo := (180846087 / 500000000)) (hi := (14467687 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717878455731 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717878455731 / 500000000000) = 1/(500000000000 / 717878455731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4016 : Bounds (180846087 / 500000000) (14467687 / 40000000) (Real.log (717878455731 / 500000000000)) := by
  have h := reflection_log_4016_neg
  have he : Real.log (717878455731 / 500000000000) = -Real.log (500000000000 / 717878455731) := by
    rw [show ((717878455731 / 500000000000) : ℝ) = ((500000000000 / 717878455731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4017_neg : (164666621 / 1000000000) ≤ -Real.log (1000 / 1179) ∧
    -Real.log (1000 / 1179) ≤ (82333311 / 500000000) := by
  have h := checkLog_sound (w := (179 / 2179)) (n := 12)
    (lo := (164666621 / 1000000000)) (hi := (82333311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1179 / 1000) = 1/(1000 / 1179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4017 : Bounds (164666621 / 1000000000) (82333311 / 500000000) (Real.log (1179 / 1000)) := by
  have h := reflection_log_4017_neg
  have he : Real.log (1179 / 1000) = -Real.log (1000 / 1179) := by
    rw [show ((1179 / 1000) : ℝ) = ((1000 / 1179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4018_neg : (197232169 / 1000000000) ≤ -Real.log (821 / 1000) ∧
    -Real.log (821 / 1000) ≤ (19723217 / 100000000) := by
  have h := checkLog_sound (w := (179 / 1821)) (n := 12)
    (lo := (197232169 / 1000000000)) (hi := (19723217 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 821) = 1/(821 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4018 : Bounds (-19723217 / 100000000) (-197232169 / 1000000000) (Real.log (821 / 1000)) := by
  have h := reflection_log_4018_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4019_neg : (178983 / 1000000000) ≤ -Real.log (1000000 / 1000179) ∧
    -Real.log (1000000 / 1000179) ≤ (22373 / 125000000) := by
  have h := checkLog_sound (w := (179 / 2000179)) (n := 12)
    (lo := (178983 / 1000000000)) (hi := (22373 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000179 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000179 / 1000000) = 1/(1000000 / 1000179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4019 : Bounds (178983 / 1000000000) (22373 / 125000000) (Real.log (1000179 / 1000000)) := by
  have h := reflection_log_4019_neg
  have he : Real.log (1000179 / 1000000) = -Real.log (1000000 / 1000179) := by
    rw [show ((1000179 / 1000000) : ℝ) = ((1000000 / 1000179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4020_neg : (22377 / 125000000) ≤ -Real.log (999821 / 1000000) ∧
    -Real.log (999821 / 1000000) ≤ (179017 / 1000000000) := by
  have h := checkLog_sound (w := (179 / 1999821)) (n := 12)
    (lo := (22377 / 125000000)) (hi := (179017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999821) = 1/(999821 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4020 : Bounds (-179017 / 1000000000) (-22377 / 125000000) (Real.log (999821 / 1000000)) := by
  have h := reflection_log_4020_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4021_neg : (86069433 / 1000000000) ≤ -Real.log (500000 / 544941) ∧
    -Real.log (500000 / 544941) ≤ (43034717 / 500000000) := by
  have h := checkLog_sound (w := (44941 / 1044941)) (n := 12)
    (lo := (86069433 / 1000000000)) (hi := (43034717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544941 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544941 / 500000) = 1/(500000 / 544941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4021 : Bounds (86069433 / 1000000000) (43034717 / 500000000) (Real.log (544941 / 500000)) := by
  have h := reflection_log_4021_neg
  have he : Real.log (544941 / 500000) = -Real.log (500000 / 544941) := by
    rw [show ((544941 / 500000) : ℝ) = ((500000 / 544941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4022_neg : (94181017 / 1000000000) ≤ -Real.log (455059 / 500000) ∧
    -Real.log (455059 / 500000) ≤ (47090509 / 500000000) := by
  have h := checkLog_sound (w := (44941 / 955059)) (n := 12)
    (lo := (94181017 / 1000000000)) (hi := (47090509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455059) = 1/(455059 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4022 : Bounds (-47090509 / 500000000) (-94181017 / 1000000000) (Real.log (455059 / 500000)) := by
  have h := reflection_log_4022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4023_neg : (86280443 / 1000000000) ≤ -Real.log (15625 / 17033) ∧
    -Real.log (15625 / 17033) ≤ (21570111 / 250000000) := by
  have h := checkLog_sound (w := (704 / 16329)) (n := 12)
    (lo := (86280443 / 1000000000)) (hi := (21570111 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17033 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17033 / 15625) = 1/(15625 / 17033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4023 : Bounds (86280443 / 1000000000) (21570111 / 250000000) (Real.log (17033 / 15625)) := by
  have h := reflection_log_4023_neg
  have he : Real.log (17033 / 15625) = -Real.log (15625 / 17033) := by
    rw [show ((17033 / 15625) : ℝ) = ((15625 / 17033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4024_neg : (94433763 / 1000000000) ≤ -Real.log (14217 / 15625) ∧
    -Real.log (14217 / 15625) ≤ (23608441 / 250000000) := by
  have h := checkLog_sound (w := (704 / 14921)) (n := 12)
    (lo := (94433763 / 1000000000)) (hi := (23608441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14217) = 1/(14217 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4024 : Bounds (-23608441 / 250000000) (-94433763 / 1000000000) (Real.log (14217 / 15625)) := by
  have h := reflection_log_4024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4025_neg : (203833 / 25000000) ≤ -Real.log (242158161 / 244140625) ∧
    -Real.log (242158161 / 244140625) ≤ (8153321 / 1000000000) := by
  have h := checkLog_sound (w := (991232 / 243149393)) (n := 12)
    (lo := (203833 / 25000000)) (hi := (8153321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242158161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242158161) = 1/(242158161 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4025 : Bounds (-8153321 / 1000000000) (-203833 / 25000000) (Real.log (242158161 / 244140625)) := by
  have h := reflection_log_4025_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4026_neg : (253487 / 31250000) ≤ -Real.log (247980306519 / 250000000000) ∧
    -Real.log (247980306519 / 250000000000) ≤ (1622317 / 200000000) := by
  have h := checkLog_sound (w := (2019693481 / 497980306519)) (n := 12)
    (lo := (253487 / 31250000)) (hi := (1622317 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247980306519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247980306519) = 1/(247980306519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4026 : Bounds (-1622317 / 200000000) (-253487 / 31250000) (Real.log (247980306519 / 250000000000)) := by
  have h := reflection_log_4026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4027_neg : (180250451 / 1000000000) ≤ -Real.log (125000000000 / 149689655627) ∧
    -Real.log (125000000000 / 149689655627) ≤ (45062613 / 250000000) := by
  have h := checkLog_sound (w := (24689655627 / 274689655627)) (n := 12)
    (lo := (180250451 / 1000000000)) (hi := (45062613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149689655627 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149689655627 / 125000000000) = 1/(125000000000 / 149689655627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4027 : Bounds (180250451 / 1000000000) (45062613 / 250000000) (Real.log (149689655627 / 125000000000)) := by
  have h := reflection_log_4027_neg
  have he : Real.log (149689655627 / 125000000000) = -Real.log (125000000000 / 149689655627) := by
    rw [show ((149689655627 / 125000000000) : ℝ) = ((125000000000 / 149689655627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4028_neg : (180714207 / 1000000000) ≤ -Real.log (125000000000 / 149759091229) ∧
    -Real.log (125000000000 / 149759091229) ≤ (5647319 / 31250000) := by
  have h := checkLog_sound (w := (24759091229 / 274759091229)) (n := 12)
    (lo := (180714207 / 1000000000)) (hi := (5647319 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149759091229 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149759091229 / 125000000000) = 1/(125000000000 / 149759091229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4028 : Bounds (180714207 / 1000000000) (5647319 / 31250000) (Real.log (149759091229 / 125000000000)) := by
  have h := reflection_log_4028_neg
  have he : Real.log (149759091229 / 125000000000) = -Real.log (125000000000 / 149759091229) := by
    rw [show ((149759091229 / 125000000000) : ℝ) = ((125000000000 / 149759091229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4029_neg : (180846087 / 500000000) ≤ -Real.log (50000000000 / 71787845573) ∧
    -Real.log (50000000000 / 71787845573) ≤ (14467687 / 40000000) := by
  have h := checkLog_sound (w := (21787845573 / 121787845573)) (n := 12)
    (lo := (180846087 / 500000000)) (hi := (14467687 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71787845573 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71787845573 / 50000000000) = 1/(50000000000 / 71787845573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4029 : Bounds (180846087 / 500000000) (14467687 / 40000000) (Real.log (71787845573 / 50000000000)) := by
  have h := reflection_log_4029_neg
  have he : Real.log (71787845573 / 50000000000) = -Real.log (50000000000 / 71787845573) := by
    rw [show ((71787845573 / 50000000000) : ℝ) = ((50000000000 / 71787845573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4030_neg : (361898791 / 1000000000) ≤ -Real.log (50000000000 / 71802679659) ∧
    -Real.log (50000000000 / 71802679659) ≤ (45237349 / 125000000) := by
  have h := checkLog_sound (w := (21802679659 / 121802679659)) (n := 12)
    (lo := (361898791 / 1000000000)) (hi := (45237349 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71802679659 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71802679659 / 50000000000) = 1/(50000000000 / 71802679659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4030 : Bounds (361898791 / 1000000000) (45237349 / 125000000) (Real.log (71802679659 / 50000000000)) := by
  have h := reflection_log_4030_neg
  have he : Real.log (71802679659 / 50000000000) = -Real.log (50000000000 / 71802679659) := by
    rw [show ((71802679659 / 50000000000) : ℝ) = ((50000000000 / 71802679659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4031_neg : (32950287 / 200000000) ≤ -Real.log (10000 / 11791) ∧
    -Real.log (10000 / 11791) ≤ (41187859 / 250000000) := by
  have h := checkLog_sound (w := (1791 / 21791)) (n := 12)
    (lo := (32950287 / 200000000)) (hi := (41187859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11791 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11791 / 10000) = 1/(10000 / 11791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4031 : Bounds (32950287 / 200000000) (41187859 / 250000000) (Real.log (11791 / 10000)) := by
  have h := reflection_log_4031_neg
  have he : Real.log (11791 / 10000) = -Real.log (10000 / 11791) := by
    rw [show ((11791 / 10000) : ℝ) = ((10000 / 11791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
