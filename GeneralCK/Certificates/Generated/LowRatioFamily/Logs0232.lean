import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14848_neg : (7356497 / 7812500) ≤ -Real.log (389991 / 1000000) ∧
    -Real.log (389991 / 1000000) ≤ (470815809 / 500000000) := by
  have h := checkLog_sound (w := (110009 / 889991)) (n := 12)
    (lo := (62121109 / 250000000)) (hi := (248484437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 389991) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 389991) = 1/(389991 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14848 : Bounds (-470815809 / 500000000) (-7356497 / 7812500) (Real.log (389991 / 1000000)) := by
  have h := reflection_log_14848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14849_neg : (58173981 / 125000000) ≤ -Real.log (627889019919 / 1000000000000) ∧
    -Real.log (627889019919 / 1000000000000) ≤ (465391849 / 1000000000) := by
  have h := checkLog_sound (w := (372110980081 / 1627889019919)) (n := 12)
    (lo := (58173981 / 125000000)) (hi := (465391849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 627889019919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 627889019919) = 1/(627889019919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14849 : Bounds (-465391849 / 1000000000) (-58173981 / 125000000) (Real.log (627889019919 / 1000000000000)) := by
  have h := reflection_log_14849_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14850_neg : (92372241 / 200000000) ≤ -Real.log (157527447351 / 250000000000) ∧
    -Real.log (157527447351 / 250000000000) ≤ (230930603 / 500000000) := by
  have h := checkLog_sound (w := (92472552649 / 407527447351)) (n := 12)
    (lo := (92372241 / 200000000)) (hi := (230930603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 157527447351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 157527447351) = 1/(157527447351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14850 : Bounds (-230930603 / 500000000) (-92372241 / 200000000) (Real.log (157527447351 / 250000000000)) := by
  have h := reflection_log_14850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14851_neg : (353018719 / 250000000) ≤ -Real.log (250000000000 / 1026115707963) ∧
    -Real.log (250000000000 / 1026115707963) ≤ (1412074879 / 1000000000) := by
  have h := checkLog_sound (w := (26115707963 / 2026115707963)) (n := 12)
    (lo := (6445129 / 250000000)) (hi := (25780517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1026115707963 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1026115707963 / 1000000000000) = 1/(250000000000 / 1026115707963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14851 : Bounds (353018719 / 250000000) (1412074879 / 1000000000) (Real.log (1026115707963 / 250000000000)) := by
  have h := reflection_log_14851_neg
  have he : Real.log (1026115707963 / 250000000000) = -Real.log (250000000000 / 1026115707963) := by
    rw [show ((1026115707963 / 250000000000) : ℝ) = ((250000000000 / 1026115707963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14852_neg : (177233923 / 125000000) ≤ -Real.log (250000000000 / 1032080868533) ∧
    -Real.log (250000000000 / 1032080868533) ≤ (1417871387 / 1000000000) := by
  have h := checkLog_sound (w := (32080868533 / 2032080868533)) (n := 12)
    (lo := (493391 / 15625000)) (hi := (1263081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1032080868533 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1032080868533 / 1000000000000) = 1/(250000000000 / 1032080868533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14852 : Bounds (177233923 / 125000000) (1417871387 / 1000000000) (Real.log (1032080868533 / 250000000000)) := by
  have h := reflection_log_14852_neg
  have he : Real.log (1032080868533 / 250000000000) = -Real.log (250000000000 / 1032080868533) := by
    rw [show ((1032080868533 / 250000000000) : ℝ) = ((250000000000 / 1032080868533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14853_neg : (3999219547 / 1000000000) ≤ -Real.log (500000000000 / 27277777777777) ∧
    -Real.log (500000000000 / 27277777777777) ≤ (3999219553 / 1000000000) := by
  have h := checkLog_sound (w := (11277777777777 / 43277777777777)) (n := 12)
    (lo := (533483647 / 1000000000)) (hi := (4167841 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27277777777777 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(27277777777777 / 16000000000000) = 1/(500000000000 / 27277777777777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14853 : Bounds (3999219547 / 1000000000) (3999219553 / 1000000000) (Real.log (27277777777777 / 500000000000)) := by
  have h := reflection_log_14853_neg
  have he : Real.log (27277777777777 / 500000000000) = -Real.log (500000000000 / 27277777777777) := by
    rw [show ((27277777777777 / 500000000000) : ℝ) = ((500000000000 / 27277777777777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14854_neg : (201394973 / 50000000) ≤ -Real.log (500000000000 / 28071428571429) ∧
    -Real.log (500000000000 / 28071428571429) ≤ (2013949733 / 500000000) := by
  have h := checkLog_sound (w := (12071428571429 / 44071428571429)) (n := 12)
    (lo := (14054089 / 25000000)) (hi := (562163561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28071428571429 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28071428571429 / 16000000000000) = 1/(500000000000 / 28071428571429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14854 : Bounds (201394973 / 50000000) (2013949733 / 500000000) (Real.log (28071428571429 / 500000000000)) := by
  have h := reflection_log_14854_neg
  have he : Real.log (28071428571429 / 500000000000) = -Real.log (500000000000 / 28071428571429) := by
    rw [show ((28071428571429 / 500000000000) : ℝ) = ((500000000000 / 28071428571429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14855_neg : (676001021 / 1000000000) ≤ -Real.log (500 / 983) ∧
    -Real.log (500 / 983) ≤ (338000511 / 500000000) := by
  have h := checkLog_sound (w := (483 / 1483)) (n := 12)
    (lo := (676001021 / 1000000000)) (hi := (338000511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983 / 500) = 1/(500 / 983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14855 : Bounds (676001021 / 1000000000) (338000511 / 500000000) (Real.log (983 / 500)) := by
  have h := reflection_log_14855_neg
  have he : Real.log (983 / 500) = -Real.log (500 / 983) := by
    rw [show ((983 / 500) : ℝ) = ((500 / 983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14856_neg : (52834293 / 15625000) ≤ -Real.log (17 / 500) ∧
    -Real.log (17 / 500) ≤ (3381394757 / 1000000000) := by
  have h := checkLog_sound (w := (57 / 193)) (n := 12)
    (lo := (38050377 / 62500000)) (hi := (608806033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 68) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 68) = 1/(17 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14856 : Bounds (-3381394757 / 1000000000) (-52834293 / 15625000) (Real.log (17 / 500)) := by
  have h := reflection_log_14856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14857_neg : (965533 / 1000000000) ≤ -Real.log (500000 / 500483) ∧
    -Real.log (500000 / 500483) ≤ (482767 / 500000000) := by
  have h := checkLog_sound (w := (483 / 1000483)) (n := 12)
    (lo := (965533 / 1000000000)) (hi := (482767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500483 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500483 / 500000) = 1/(500000 / 500483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14857 : Bounds (965533 / 1000000000) (482767 / 500000000) (Real.log (500483 / 500000)) := by
  have h := reflection_log_14857_neg
  have he : Real.log (500483 / 500000) = -Real.log (500000 / 500483) := by
    rw [show ((500483 / 500000) : ℝ) = ((500000 / 500483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14858_neg : (483233 / 500000000) ≤ -Real.log (499517 / 500000) ∧
    -Real.log (499517 / 500000) ≤ (966467 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 999517)) (n := 12)
    (lo := (483233 / 500000000)) (hi := (966467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499517) = 1/(499517 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14858 : Bounds (-966467 / 1000000000) (-483233 / 500000000) (Real.log (499517 / 500000)) := by
  have h := reflection_log_14858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14859_neg : (475835341 / 1000000000) ≤ -Real.log (500000 / 804679) ∧
    -Real.log (500000 / 804679) ≤ (237917671 / 500000000) := by
  have h := checkLog_sound (w := (304679 / 1304679)) (n := 12)
    (lo := (475835341 / 1000000000)) (hi := (237917671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804679 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804679 / 500000) = 1/(500000 / 804679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14859 : Bounds (475835341 / 1000000000) (237917671 / 500000000) (Real.log (804679 / 500000)) := by
  have h := reflection_log_14859_neg
  have he : Real.log (804679 / 500000) = -Real.log (500000 / 804679) := by
    rw [show ((804679 / 500000) : ℝ) = ((500000 / 804679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14860_neg : (469981869 / 500000000) ≤ -Real.log (195321 / 500000) ∧
    -Real.log (195321 / 500000) ≤ (46998187 / 50000000) := by
  have h := checkLog_sound (w := (54679 / 445321)) (n := 12)
    (lo := (123408279 / 500000000)) (hi := (246816559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195321) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 195321) = 1/(195321 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14860 : Bounds (-46998187 / 50000000) (-469981869 / 500000000) (Real.log (195321 / 500000)) := by
  have h := reflection_log_14860_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14861_neg : (95394359 / 200000000) ≤ -Real.log (250000 / 402797) ∧
    -Real.log (250000 / 402797) ≤ (119242949 / 250000000) := by
  have h := checkLog_sound (w := (152797 / 652797)) (n := 12)
    (lo := (95394359 / 200000000)) (hi := (119242949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((402797 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(402797 / 250000) = 1/(250000 / 402797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14861 : Bounds (95394359 / 200000000) (119242949 / 250000000) (Real.log (402797 / 250000)) := by
  have h := reflection_log_14861_neg
  have he : Real.log (402797 / 250000) = -Real.log (250000 / 402797) := by
    rw [show ((402797 / 250000) : ℝ) = ((250000 / 402797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14862_neg : (472329671 / 500000000) ≤ -Real.log (97203 / 250000) ∧
    -Real.log (97203 / 250000) ≤ (59041209 / 62500000) := by
  have h := checkLog_sound (w := (27797 / 222203)) (n := 12)
    (lo := (125756081 / 500000000)) (hi := (251512163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 97203) = 1/(97203 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14862 : Bounds (-59041209 / 62500000) (-472329671 / 500000000) (Real.log (97203 / 250000)) := by
  have h := reflection_log_14862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14863_neg : (467687547 / 1000000000) ≤ -Real.log (39153076791 / 62500000000) ∧
    -Real.log (39153076791 / 62500000000) ≤ (116921887 / 250000000) := by
  have h := checkLog_sound (w := (23346923209 / 101653076791)) (n := 12)
    (lo := (467687547 / 1000000000)) (hi := (116921887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 39153076791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 39153076791) = 1/(39153076791 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14863 : Bounds (-116921887 / 250000000) (-467687547 / 1000000000) (Real.log (39153076791 / 62500000000)) := by
  have h := reflection_log_14863_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14864_neg : (464128397 / 1000000000) ≤ -Real.log (157170706959 / 250000000000) ∧
    -Real.log (157170706959 / 250000000000) ≤ (232064199 / 500000000) := by
  have h := checkLog_sound (w := (92829293041 / 407170706959)) (n := 12)
    (lo := (464128397 / 1000000000)) (hi := (232064199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 157170706959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 157170706959) = 1/(157170706959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14864 : Bounds (-232064199 / 500000000) (-464128397 / 1000000000) (Real.log (157170706959 / 250000000000)) := by
  have h := reflection_log_14864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14865_neg : (35394977 / 25000000) ≤ -Real.log (31250000000 / 128743037103) ∧
    -Real.log (31250000000 / 128743037103) ≤ (1415799083 / 1000000000) := by
  have h := checkLog_sound (w := (3743037103 / 253743037103)) (n := 12)
    (lo := (368809 / 12500000)) (hi := (29504721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128743037103 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(128743037103 / 125000000000) = 1/(31250000000 / 128743037103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14865 : Bounds (35394977 / 25000000) (1415799083 / 1000000000) (Real.log (128743037103 / 31250000000)) := by
  have h := reflection_log_14865_neg
  have he : Real.log (128743037103 / 31250000000) = -Real.log (31250000000 / 128743037103) := by
    rw [show ((128743037103 / 31250000000) : ℝ) = ((31250000000 / 128743037103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14866_neg : (44425973 / 31250000) ≤ -Real.log (125000000000 / 517984270033) ∧
    -Real.log (125000000000 / 517984270033) ≤ (1421631139 / 1000000000) := by
  have h := checkLog_sound (w := (17984270033 / 1017984270033)) (n := 12)
    (lo := (4417097 / 125000000)) (hi := (35336777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517984270033 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(517984270033 / 500000000000) = 1/(125000000000 / 517984270033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14866 : Bounds (44425973 / 31250000) (1421631139 / 1000000000) (Real.log (517984270033 / 125000000000)) := by
  have h := reflection_log_14866_neg
  have he : Real.log (517984270033 / 125000000000) = -Real.log (125000000000 / 517984270033) := by
    rw [show ((517984270033 / 125000000000) : ℝ) = ((125000000000 / 517984270033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14867_neg : (201394973 / 50000000) ≤ -Real.log (125000000000 / 7017857142857) ∧
    -Real.log (125000000000 / 7017857142857) ≤ (2013949733 / 500000000) := by
  have h := checkLog_sound (w := (3017857142857 / 11017857142857)) (n := 12)
    (lo := (14054089 / 25000000)) (hi := (562163561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7017857142857 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7017857142857 / 4000000000000) = 1/(125000000000 / 7017857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14867 : Bounds (201394973 / 50000000) (2013949733 / 500000000) (Real.log (7017857142857 / 125000000000)) := by
  have h := reflection_log_14867_neg
  have he : Real.log (7017857142857 / 125000000000) = -Real.log (125000000000 / 7017857142857) := by
    rw [show ((7017857142857 / 125000000000) : ℝ) = ((125000000000 / 7017857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14868_neg : (4057395773 / 1000000000) ≤ -Real.log (500000000000 / 28911764705883) ∧
    -Real.log (500000000000 / 28911764705883) ≤ (4057395779 / 1000000000) := by
  have h := checkLog_sound (w := (12911764705883 / 44911764705883)) (n := 12)
    (lo := (591659873 / 1000000000)) (hi := (295829937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28911764705883 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28911764705883 / 16000000000000) = 1/(500000000000 / 28911764705883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14868 : Bounds (4057395773 / 1000000000) (4057395779 / 1000000000) (Real.log (28911764705883 / 500000000000)) := by
  have h := reflection_log_14868_neg
  have he : Real.log (28911764705883 / 500000000000) = -Real.log (500000000000 / 28911764705883) := by
    rw [show ((28911764705883 / 500000000000) : ℝ) = ((500000000000 / 28911764705883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14869_neg : (676509539 / 1000000000) ≤ -Real.log (1000 / 1967) ∧
    -Real.log (1000 / 1967) ≤ (33825477 / 50000000) := by
  have h := checkLog_sound (w := (967 / 2967)) (n := 12)
    (lo := (676509539 / 1000000000)) (hi := (33825477 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1967 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1967 / 1000) = 1/(1000 / 1967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14869 : Bounds (676509539 / 1000000000) (33825477 / 50000000) (Real.log (1967 / 1000)) := by
  have h := reflection_log_14869_neg
  have he : Real.log (1967 / 1000) = -Real.log (1000 / 1967) := by
    rw [show ((1967 / 1000) : ℝ) = ((1000 / 1967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14870_neg : (682249543 / 200000000) ≤ -Real.log (33 / 1000) ∧
    -Real.log (33 / 1000) ≤ (85281193 / 25000000) := by
  have h := checkLog_sound (w := (59 / 191)) (n := 12)
    (lo := (127731799 / 200000000)) (hi := (159664749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 66) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 66) = 1/(33 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14870 : Bounds (-85281193 / 25000000) (-682249543 / 200000000) (Real.log (33 / 1000)) := by
  have h := reflection_log_14870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14871_neg : (241633 / 250000000) ≤ -Real.log (1000000 / 1000967) ∧
    -Real.log (1000000 / 1000967) ≤ (966533 / 1000000000) := by
  have h := checkLog_sound (w := (967 / 2000967)) (n := 12)
    (lo := (241633 / 250000000)) (hi := (966533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000967 / 1000000) = 1/(1000000 / 1000967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14871 : Bounds (241633 / 250000000) (966533 / 1000000000) (Real.log (1000967 / 1000000)) := by
  have h := reflection_log_14871_neg
  have he : Real.log (1000967 / 1000000) = -Real.log (1000000 / 1000967) := by
    rw [show ((1000967 / 1000000) : ℝ) = ((1000000 / 1000967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14872_neg : (967467 / 1000000000) ≤ -Real.log (999033 / 1000000) ∧
    -Real.log (999033 / 1000000) ≤ (241867 / 250000000) := by
  have h := checkLog_sound (w := (967 / 1999033)) (n := 12)
    (lo := (967467 / 1000000000)) (hi := (241867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999033) = 1/(999033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14872 : Bounds (-241867 / 250000000) (-967467 / 1000000000) (Real.log (999033 / 1000000)) := by
  have h := reflection_log_14872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14873_neg : (476567663 / 1000000000) ≤ -Real.log (1000000 / 1610537) ∧
    -Real.log (1000000 / 1610537) ≤ (29785479 / 62500000) := by
  have h := checkLog_sound (w := (610537 / 2610537)) (n := 12)
    (lo := (476567663 / 1000000000)) (hi := (29785479 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1610537 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1610537 / 1000000) = 1/(1000000 / 1610537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14873 : Bounds (476567663 / 1000000000) (29785479 / 62500000) (Real.log (1610537 / 1000000)) := by
  have h := reflection_log_14873_neg
  have he : Real.log (1610537 / 1000000) = -Real.log (1000000 / 1610537) := by
    rw [show ((1610537 / 1000000) : ℝ) = ((1000000 / 1610537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14874_neg : (942986411 / 1000000000) ≤ -Real.log (389463 / 1000000) ∧
    -Real.log (389463 / 1000000) ≤ (942986413 / 1000000000) := by
  have h := checkLog_sound (w := (110537 / 889463)) (n := 12)
    (lo := (249839231 / 1000000000)) (hi := (1951869 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 389463) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 389463) = 1/(389463 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14874 : Bounds (-942986413 / 1000000000) (-942986411 / 1000000000) (Real.log (389463 / 1000000)) := by
  have h := reflection_log_14874_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14875_neg : (238853503 / 500000000) ≤ -Real.log (1000000 / 1612373) ∧
    -Real.log (1000000 / 1612373) ≤ (477707007 / 1000000000) := by
  have h := checkLog_sound (w := (612373 / 2612373)) (n := 12)
    (lo := (238853503 / 500000000)) (hi := (477707007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1612373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1612373 / 1000000) = 1/(1000000 / 1612373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14875 : Bounds (238853503 / 500000000) (477707007 / 1000000000) (Real.log (1612373 / 1000000)) := by
  have h := reflection_log_14875_neg
  have he : Real.log (1612373 / 1000000) = -Real.log (1000000 / 1612373) := by
    rw [show ((1612373 / 1000000) : ℝ) = ((1000000 / 1612373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14876_neg : (947711741 / 1000000000) ≤ -Real.log (387627 / 1000000) ∧
    -Real.log (387627 / 1000000) ≤ (947711743 / 1000000000) := by
  have h := checkLog_sound (w := (112373 / 887627)) (n := 12)
    (lo := (254564561 / 1000000000)) (hi := (127282281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387627) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 387627) = 1/(387627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14876 : Bounds (-947711743 / 1000000000) (-947711741 / 1000000000) (Real.log (387627 / 1000000)) := by
  have h := reflection_log_14876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14877_neg : (94000947 / 200000000) ≤ -Real.log (624999308871 / 1000000000000) ∧
    -Real.log (624999308871 / 1000000000000) ≤ (917978 / 1953125) := by
  have h := checkLog_sound (w := (375000691129 / 1624999308871)) (n := 12)
    (lo := (94000947 / 200000000)) (hi := (917978 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 624999308871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 624999308871) = 1/(624999308871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14877 : Bounds (-917978 / 1953125) (-94000947 / 200000000) (Real.log (624999308871 / 1000000000000)) := by
  have h := reflection_log_14877_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14878_neg : (116604687 / 250000000) ≤ -Real.log (627244571631 / 1000000000000) ∧
    -Real.log (627244571631 / 1000000000000) ≤ (466418749 / 1000000000) := by
  have h := checkLog_sound (w := (372755428369 / 1627244571631)) (n := 12)
    (lo := (116604687 / 250000000)) (hi := (466418749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 627244571631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 627244571631) = 1/(627244571631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14878 : Bounds (-466418749 / 1000000000) (-116604687 / 250000000) (Real.log (627244571631 / 1000000000000)) := by
  have h := reflection_log_14878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14879_neg : (709777037 / 500000000) ≤ -Real.log (500000000000 / 2067638004123) ∧
    -Real.log (500000000000 / 2067638004123) ≤ (1419554077 / 1000000000) := by
  have h := checkLog_sound (w := (67638004123 / 4067638004123)) (n := 12)
    (lo := (16629857 / 500000000)) (hi := (6651943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2067638004123 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2067638004123 / 2000000000000) = 1/(500000000000 / 2067638004123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14879 : Bounds (709777037 / 500000000) (1419554077 / 1000000000) (Real.log (2067638004123 / 500000000000)) := by
  have h := reflection_log_14879_neg
  have he : Real.log (2067638004123 / 500000000000) = -Real.log (500000000000 / 2067638004123) := by
    rw [show ((2067638004123 / 500000000000) : ℝ) = ((500000000000 / 2067638004123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14880_neg : (1425418747 / 1000000000) ≤ -Real.log (500000000000 / 2079799652759) ∧
    -Real.log (500000000000 / 2079799652759) ≤ (228067 / 160000) := by
  have h := checkLog_sound (w := (79799652759 / 4079799652759)) (n := 12)
    (lo := (39124387 / 1000000000)) (hi := (9781097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2079799652759 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2079799652759 / 2000000000000) = 1/(500000000000 / 2079799652759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14880 : Bounds (1425418747 / 1000000000) (228067 / 160000) (Real.log (2079799652759 / 500000000000)) := by
  have h := reflection_log_14880_neg
  have he : Real.log (2079799652759 / 500000000000) = -Real.log (500000000000 / 2079799652759) := by
    rw [show ((2079799652759 / 500000000000) : ℝ) = ((500000000000 / 2079799652759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14881_neg : (4057395773 / 1000000000) ≤ -Real.log (250000000000 / 14455882352941) ∧
    -Real.log (250000000000 / 14455882352941) ≤ (4057395779 / 1000000000) := by
  have h := checkLog_sound (w := (6455882352941 / 22455882352941)) (n := 12)
    (lo := (591659873 / 1000000000)) (hi := (295829937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14455882352941 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(14455882352941 / 8000000000000) = 1/(250000000000 / 14455882352941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14881 : Bounds (4057395773 / 1000000000) (4057395779 / 1000000000) (Real.log (14455882352941 / 250000000000)) := by
  have h := reflection_log_14881_neg
  have he : Real.log (14455882352941 / 250000000000) = -Real.log (250000000000 / 14455882352941) := by
    rw [show ((14455882352941 / 250000000000) : ℝ) = ((250000000000 / 14455882352941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14882_neg : (2043878627 / 500000000) ≤ -Real.log (500000000000 / 29803030303031) ∧
    -Real.log (500000000000 / 29803030303031) ≤ (204387863 / 50000000) := by
  have h := checkLog_sound (w := (13803030303031 / 45803030303031)) (n := 12)
    (lo := (311010677 / 500000000)) (hi := (124404271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29803030303031 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(29803030303031 / 16000000000000) = 1/(500000000000 / 29803030303031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14882 : Bounds (2043878627 / 500000000) (204387863 / 50000000) (Real.log (29803030303031 / 500000000000)) := by
  have h := reflection_log_14882_neg
  have he : Real.log (29803030303031 / 500000000000) = -Real.log (500000000000 / 29803030303031) := by
    rw [show ((29803030303031 / 500000000000) : ℝ) = ((500000000000 / 29803030303031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14883_neg : (338508899 / 500000000) ≤ -Real.log (125 / 246) ∧
    -Real.log (125 / 246) ≤ (677017799 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 371)) (n := 12)
    (lo := (338508899 / 500000000)) (hi := (677017799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246 / 125) = 1/(125 / 246) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14883 : Bounds (338508899 / 500000000) (677017799 / 1000000000) (Real.log (246 / 125)) := by
  have h := reflection_log_14883_neg
  have he : Real.log (246 / 125) = -Real.log (125 / 246) := by
    rw [show ((246 / 125) : ℝ) = ((125 / 246) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14884_neg : (3442019373 / 1000000000) ≤ -Real.log (4 / 125) ∧
    -Real.log (4 / 125) ≤ (1721009689 / 500000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 64) = 1/(4 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14884 : Bounds (-1721009689 / 500000000) (-3442019373 / 1000000000) (Real.log (4 / 125)) := by
  have h := reflection_log_14884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14885_neg : (967531 / 1000000000) ≤ -Real.log (125000 / 125121) ∧
    -Real.log (125000 / 125121) ≤ (241883 / 250000000) := by
  have h := checkLog_sound (w := (121 / 250121)) (n := 12)
    (lo := (967531 / 1000000000)) (hi := (241883 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125121 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125121 / 125000) = 1/(125000 / 125121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14885 : Bounds (967531 / 1000000000) (241883 / 250000000) (Real.log (125121 / 125000)) := by
  have h := reflection_log_14885_neg
  have he : Real.log (125121 / 125000) = -Real.log (125000 / 125121) := by
    rw [show ((125121 / 125000) : ℝ) = ((125000 / 125121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14886_neg : (242117 / 250000000) ≤ -Real.log (124879 / 125000) ∧
    -Real.log (124879 / 125000) ≤ (968469 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 249879)) (n := 12)
    (lo := (242117 / 250000000)) (hi := (968469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124879) = 1/(124879 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14886 : Bounds (-968469 / 1000000000) (-242117 / 250000000) (Real.log (124879 / 125000)) := by
  have h := reflection_log_14886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14887_neg : (119325793 / 250000000) ≤ -Real.log (500000 / 805861) ∧
    -Real.log (500000 / 805861) ≤ (477303173 / 1000000000) := by
  have h := checkLog_sound (w := (305861 / 1305861)) (n := 12)
    (lo := (119325793 / 250000000)) (hi := (477303173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805861 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805861 / 500000) = 1/(500000 / 805861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14887 : Bounds (119325793 / 250000000) (477303173 / 1000000000) (Real.log (805861 / 500000)) := by
  have h := reflection_log_14887_neg
  have he : Real.log (805861 / 500000) = -Real.log (500000 / 805861) := by
    rw [show ((805861 / 500000) : ℝ) = ((500000 / 805861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14888_neg : (9460337 / 10000000) ≤ -Real.log (194139 / 500000) ∧
    -Real.log (194139 / 500000) ≤ (473016851 / 500000000) := by
  have h := checkLog_sound (w := (55861 / 444139)) (n := 12)
    (lo := (6322163 / 25000000)) (hi := (252886521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194139) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 194139) = 1/(194139 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14888 : Bounds (-473016851 / 500000000) (-9460337 / 10000000) (Real.log (194139 / 500000)) := by
  have h := reflection_log_14888_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14889_neg : (7475719 / 15625000) ≤ -Real.log (200000 / 322713) ∧
    -Real.log (200000 / 322713) ≤ (478446017 / 1000000000) := by
  have h := checkLog_sound (w := (122713 / 522713)) (n := 12)
    (lo := (7475719 / 15625000)) (hi := (478446017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322713 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322713 / 200000) = 1/(200000 / 322713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14889 : Bounds (7475719 / 15625000) (478446017 / 1000000000) (Real.log (322713 / 200000)) := by
  have h := reflection_log_14889_neg
  have he : Real.log (322713 / 200000) = -Real.log (200000 / 322713) := by
    rw [show ((322713 / 200000) : ℝ) = ((200000 / 322713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14890_neg : (2376979 / 2500000) ≤ -Real.log (77287 / 200000) ∧
    -Real.log (77287 / 200000) ≤ (475395801 / 500000000) := by
  have h := checkLog_sound (w := (22713 / 177287)) (n := 12)
    (lo := (12882221 / 50000000)) (hi := (257644421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 77287) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 77287) = 1/(77287 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14890 : Bounds (-475395801 / 500000000) (-2376979 / 2500000) (Real.log (77287 / 200000)) := by
  have h := reflection_log_14890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14891_neg : (29521599 / 62500000) ≤ -Real.log (24941519631 / 40000000000) ∧
    -Real.log (24941519631 / 40000000000) ≤ (94469117 / 200000000) := by
  have h := checkLog_sound (w := (15058480369 / 64941519631)) (n := 12)
    (lo := (29521599 / 62500000)) (hi := (94469117 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 24941519631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 24941519631) = 1/(24941519631 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14891 : Bounds (-94469117 / 200000000) (-29521599 / 62500000) (Real.log (24941519631 / 40000000000)) := by
  have h := reflection_log_14891_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14892_neg : (14647829 / 31250000) ≤ -Real.log (156449048679 / 250000000000) ∧
    -Real.log (156449048679 / 250000000000) ≤ (468730529 / 1000000000) := by
  have h := checkLog_sound (w := (93550951321 / 406449048679)) (n := 12)
    (lo := (14647829 / 31250000)) (hi := (468730529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 156449048679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 156449048679) = 1/(156449048679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14892 : Bounds (-468730529 / 1000000000) (-14647829 / 31250000) (Real.log (156449048679 / 250000000000)) := by
  have h := reflection_log_14892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14893_neg : (177917109 / 125000000) ≤ -Real.log (500000000000 / 2075474273587) ∧
    -Real.log (500000000000 / 2075474273587) ≤ (2277339 / 1600000) := by
  have h := checkLog_sound (w := (75474273587 / 4075474273587)) (n := 12)
    (lo := (2315157 / 62500000)) (hi := (37042513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2075474273587 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2075474273587 / 2000000000000) = 1/(500000000000 / 2075474273587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14893 : Bounds (177917109 / 125000000) (2277339 / 1600000) (Real.log (2075474273587 / 500000000000)) := by
  have h := reflection_log_14893_neg
  have he : Real.log (2075474273587 / 500000000000) = -Real.log (500000000000 / 2075474273587) := by
    rw [show ((2075474273587 / 500000000000) : ℝ) = ((500000000000 / 2075474273587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14894_neg : (89327351 / 62500000) ≤ -Real.log (500000000000 / 2087757320119) ∧
    -Real.log (500000000000 / 2087757320119) ≤ (1429237619 / 1000000000) := by
  have h := checkLog_sound (w := (87757320119 / 4087757320119)) (n := 12)
    (lo := (5367907 / 125000000)) (hi := (42943257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2087757320119 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2087757320119 / 2000000000000) = 1/(500000000000 / 2087757320119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14894 : Bounds (89327351 / 62500000) (1429237619 / 1000000000) (Real.log (2087757320119 / 500000000000)) := by
  have h := reflection_log_14894_neg
  have he : Real.log (2087757320119 / 500000000000) = -Real.log (500000000000 / 2087757320119) := by
    rw [show ((2087757320119 / 500000000000) : ℝ) = ((500000000000 / 2087757320119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14895_neg : (2043878627 / 500000000) ≤ -Real.log (50000000000 / 2980303030303) ∧
    -Real.log (50000000000 / 2980303030303) ≤ (204387863 / 50000000) := by
  have h := checkLog_sound (w := (1380303030303 / 4580303030303)) (n := 12)
    (lo := (311010677 / 500000000)) (hi := (124404271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2980303030303 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2980303030303 / 1600000000000) = 1/(50000000000 / 2980303030303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14895 : Bounds (2043878627 / 500000000) (204387863 / 50000000) (Real.log (2980303030303 / 50000000000)) := by
  have h := reflection_log_14895_neg
  have he : Real.log (2980303030303 / 50000000000) = -Real.log (50000000000 / 2980303030303) := by
    rw [show ((2980303030303 / 50000000000) : ℝ) = ((50000000000 / 2980303030303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14896_neg : (1029759293 / 250000000) ≤ -Real.log (2 / 123) ∧
    -Real.log (2 / 123) ≤ (2059518589 / 500000000) := by
  have h := checkLog_sound (w := (59 / 187)) (n := 12)
    (lo := (81662659 / 125000000)) (hi := (653301273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123 / 64) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(123 / 64) = 1/(2 / 123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14896 : Bounds (1029759293 / 250000000) (2059518589 / 500000000) (Real.log (123 / 2)) := by
  have h := reflection_log_14896_neg
  have he : Real.log (123 / 2) = -Real.log (2 / 123) := by
    rw [show ((123 / 2) : ℝ) = ((2 / 123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14897_neg : (677525799 / 1000000000) ≤ -Real.log (1000 / 1969) ∧
    -Real.log (1000 / 1969) ≤ (3387629 / 5000000) := by
  have h := checkLog_sound (w := (969 / 2969)) (n := 12)
    (lo := (677525799 / 1000000000)) (hi := (3387629 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969 / 1000) = 1/(1000 / 1969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14897 : Bounds (677525799 / 1000000000) (3387629 / 5000000) (Real.log (1969 / 1000)) := by
  have h := reflection_log_14897_neg
  have he : Real.log (1969 / 1000) = -Real.log (1000 / 1969) := by
    rw [show ((1969 / 1000) : ℝ) = ((1000 / 1969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14898_neg : (3473768071 / 1000000000) ≤ -Real.log (31 / 1000) ∧
    -Real.log (31 / 1000) ≤ (3473768077 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 249)) (n := 12)
    (lo := (8032171 / 1000000000)) (hi := (2008043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 124) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 124) = 1/(31 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14898 : Bounds (-3473768077 / 1000000000) (-3473768071 / 1000000000) (Real.log (31 / 1000)) := by
  have h := reflection_log_14898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14899_neg : (96853 / 100000000) ≤ -Real.log (1000000 / 1000969) ∧
    -Real.log (1000000 / 1000969) ≤ (968531 / 1000000000) := by
  have h := checkLog_sound (w := (969 / 2000969)) (n := 12)
    (lo := (96853 / 100000000)) (hi := (968531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000969 / 1000000) = 1/(1000000 / 1000969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14899 : Bounds (96853 / 100000000) (968531 / 1000000000) (Real.log (1000969 / 1000000)) := by
  have h := reflection_log_14899_neg
  have he : Real.log (1000969 / 1000000) = -Real.log (1000000 / 1000969) := by
    rw [show ((1000969 / 1000000) : ℝ) = ((1000000 / 1000969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14900_neg : (969469 / 1000000000) ≤ -Real.log (999031 / 1000000) ∧
    -Real.log (999031 / 1000000) ≤ (96947 / 100000000) := by
  have h := checkLog_sound (w := (969 / 1999031)) (n := 12)
    (lo := (969469 / 1000000000)) (hi := (96947 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999031) = 1/(999031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14900 : Bounds (-96947 / 100000000) (-969469 / 1000000000) (Real.log (999031 / 1000000)) := by
  have h := reflection_log_14900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14901_neg : (4780431 / 10000000) ≤ -Real.log (200000 / 322583) ∧
    -Real.log (200000 / 322583) ≤ (478043101 / 1000000000) := by
  have h := checkLog_sound (w := (122583 / 522583)) (n := 12)
    (lo := (4780431 / 10000000)) (hi := (478043101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322583 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(322583 / 200000) = 1/(200000 / 322583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14901 : Bounds (4780431 / 10000000) (478043101 / 1000000000) (Real.log (322583 / 200000)) := by
  have h := reflection_log_14901_neg
  have he : Real.log (322583 / 200000) = -Real.log (200000 / 322583) := by
    rw [show ((322583 / 200000) : ℝ) = ((200000 / 322583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14902_neg : (949110971 / 1000000000) ≤ -Real.log (77417 / 200000) ∧
    -Real.log (77417 / 200000) ≤ (949110973 / 1000000000) := by
  have h := checkLog_sound (w := (22583 / 177417)) (n := 12)
    (lo := (255963791 / 1000000000)) (hi := (15997737 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 77417) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 77417) = 1/(77417 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14902 : Bounds (-949110973 / 1000000000) (-949110971 / 1000000000) (Real.log (77417 / 200000)) := by
  have h := reflection_log_14902_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14903_neg : (95837763 / 200000000) ≤ -Real.log (250000 / 403691) ∧
    -Real.log (250000 / 403691) ≤ (29949301 / 62500000) := by
  have h := checkLog_sound (w := (153691 / 653691)) (n := 12)
    (lo := (95837763 / 200000000)) (hi := (29949301 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403691 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403691 / 250000) = 1/(250000 / 403691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14903 : Bounds (95837763 / 200000000) (29949301 / 62500000) (Real.log (403691 / 250000)) := by
  have h := reflection_log_14903_neg
  have he : Real.log (403691 / 250000) = -Real.log (250000 / 403691) := by
    rw [show ((403691 / 250000) : ℝ) = ((250000 / 403691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14904_neg : (119237393 / 125000000) ≤ -Real.log (96309 / 250000) ∧
    -Real.log (96309 / 250000) ≤ (476949573 / 500000000) := by
  have h := checkLog_sound (w := (28691 / 221309)) (n := 12)
    (lo := (65187991 / 250000000)) (hi := (52150393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96309) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 96309) = 1/(96309 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14904 : Bounds (-476949573 / 500000000) (-119237393 / 125000000) (Real.log (96309 / 250000)) := by
  have h := reflection_log_14904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14905_neg : (474710329 / 1000000000) ≤ -Real.log (38879076519 / 62500000000) ∧
    -Real.log (38879076519 / 62500000000) ≤ (47471033 / 100000000) := by
  have h := checkLog_sound (w := (23620923481 / 101379076519)) (n := 12)
    (lo := (474710329 / 1000000000)) (hi := (47471033 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 38879076519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 38879076519) = 1/(38879076519 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14905 : Bounds (-47471033 / 100000000) (-474710329 / 1000000000) (Real.log (38879076519 / 62500000000)) := by
  have h := reflection_log_14905_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14906_neg : (47106787 / 100000000) ≤ -Real.log (24973408111 / 40000000000) ∧
    -Real.log (24973408111 / 40000000000) ≤ (471067871 / 1000000000) := by
  have h := checkLog_sound (w := (15026591889 / 64973408111)) (n := 12)
    (lo := (47106787 / 100000000)) (hi := (471067871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 24973408111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 24973408111) = 1/(24973408111 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14906 : Bounds (-471067871 / 1000000000) (-47106787 / 100000000) (Real.log (24973408111 / 40000000000)) := by
  have h := reflection_log_14906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14907_neg : (1427154071 / 1000000000) ≤ -Real.log (31250000000 / 130213244507) ∧
    -Real.log (31250000000 / 130213244507) ≤ (713577037 / 500000000) := by
  have h := checkLog_sound (w := (5213244507 / 255213244507)) (n := 12)
    (lo := (40859711 / 1000000000)) (hi := (638433 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130213244507 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(130213244507 / 125000000000) = 1/(31250000000 / 130213244507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14907 : Bounds (1427154071 / 1000000000) (713577037 / 500000000) (Real.log (130213244507 / 31250000000)) := by
  have h := reflection_log_14907_neg
  have he : Real.log (130213244507 / 31250000000) = -Real.log (31250000000 / 130213244507) := by
    rw [show ((130213244507 / 31250000000) : ℝ) = ((31250000000 / 130213244507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14908_neg : (35827199 / 25000000) ≤ -Real.log (62500000000 / 261976424841) ∧
    -Real.log (62500000000 / 261976424841) ≤ (1433087963 / 1000000000) := by
  have h := checkLog_sound (w := (11976424841 / 511976424841)) (n := 12)
    (lo := (14623 / 312500)) (hi := (46793601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261976424841 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(261976424841 / 250000000000) = 1/(62500000000 / 261976424841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14908 : Bounds (35827199 / 25000000) (1433087963 / 1000000000) (Real.log (261976424841 / 62500000000)) := by
  have h := reflection_log_14908_neg
  have he : Real.log (261976424841 / 62500000000) = -Real.log (62500000000 / 261976424841) := by
    rw [show ((261976424841 / 62500000000) : ℝ) = ((62500000000 / 261976424841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14909_neg : (4151293871 / 1000000000) ≤ -Real.log (50000000000 / 3175806451613) ∧
    -Real.log (50000000000 / 3175806451613) ≤ (4151293877 / 1000000000) := by
  have h := checkLog_sound (w := (1575806451613 / 4775806451613)) (n := 12)
    (lo := (685557971 / 1000000000)) (hi := (171389493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3175806451613 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3175806451613 / 1600000000000) = 1/(50000000000 / 3175806451613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14909 : Bounds (4151293871 / 1000000000) (4151293877 / 1000000000) (Real.log (3175806451613 / 50000000000)) := by
  have h := reflection_log_14909_neg
  have he : Real.log (3175806451613 / 50000000000) = -Real.log (50000000000 / 3175806451613) := by
    rw [show ((3175806451613 / 50000000000) : ℝ) = ((50000000000 / 3175806451613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14910_neg : (339016771 / 500000000) ≤ -Real.log (100 / 197) ∧
    -Real.log (100 / 197) ≤ (678033543 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 297)) (n := 12)
    (lo := (339016771 / 500000000)) (hi := (678033543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197 / 100) = 1/(100 / 197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14910 : Bounds (339016771 / 500000000) (678033543 / 1000000000) (Real.log (197 / 100)) := by
  have h := reflection_log_14910_neg
  have he : Real.log (197 / 100) = -Real.log (100 / 197) := by
    rw [show ((197 / 100) : ℝ) = ((100 / 197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14911_neg : (1753278947 / 500000000) ≤ -Real.log (3 / 100) ∧
    -Real.log (3 / 100) ≤ (35065579 / 10000000) := by
  have h := checkLog_sound (w := (1 / 49)) (n := 12)
    (lo := (20410997 / 500000000)) (hi := (8164399 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 24) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25 / 24) = 1/(3 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14911 : Bounds (-35065579 / 10000000) (-1753278947 / 500000000) (Real.log (3 / 100)) := by
  have h := reflection_log_14911_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
