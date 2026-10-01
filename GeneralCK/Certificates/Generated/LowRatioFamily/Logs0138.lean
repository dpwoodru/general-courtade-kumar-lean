import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8832_neg : (145470957 / 1000000000) ≤ -Real.log (172923 / 200000) ∧
    -Real.log (172923 / 200000) ≤ (72735479 / 500000000) := by
  have h := checkLog_sound (w := (27077 / 372923)) (n := 12)
    (lo := (145470957 / 1000000000)) (hi := (72735479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 172923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 172923) = 1/(172923 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8832 : Bounds (-72735479 / 500000000) (-145470957 / 1000000000) (Real.log (172923 / 200000)) := by
  have h := reflection_log_8832_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8833_neg : (18499157 / 1000000000) ≤ -Real.log (39266836071 / 40000000000) ∧
    -Real.log (39266836071 / 40000000000) ≤ (9249579 / 500000000) := by
  have h := checkLog_sound (w := (733163929 / 79266836071)) (n := 12)
    (lo := (18499157 / 1000000000)) (hi := (9249579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39266836071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39266836071) = 1/(39266836071 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8833 : Bounds (-9249579 / 500000000) (-18499157 / 1000000000) (Real.log (39266836071 / 40000000000)) := by
  have h := reflection_log_8833_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8834_neg : (9177457 / 500000000) ≤ -Real.log (981812510679 / 1000000000000) ∧
    -Real.log (981812510679 / 1000000000000) ≤ (3670983 / 200000000) := by
  have h := checkLog_sound (w := (18187489321 / 1981812510679)) (n := 12)
    (lo := (9177457 / 500000000)) (hi := (3670983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981812510679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981812510679) = 1/(981812510679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8834 : Bounds (-3670983 / 200000000) (-9177457 / 500000000) (Real.log (981812510679 / 1000000000000)) := by
  have h := reflection_log_8834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8835_neg : (271375267 / 1000000000) ≤ -Real.log (500000000000 / 655883621013) ∧
    -Real.log (500000000000 / 655883621013) ≤ (67843817 / 250000000) := by
  have h := checkLog_sound (w := (155883621013 / 1155883621013)) (n := 12)
    (lo := (271375267 / 1000000000)) (hi := (67843817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655883621013 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655883621013 / 500000000000) = 1/(500000000000 / 655883621013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8835 : Bounds (271375267 / 1000000000) (67843817 / 250000000) (Real.log (655883621013 / 500000000000)) := by
  have h := reflection_log_8835_neg
  have he : Real.log (655883621013 / 500000000000) = -Real.log (500000000000 / 655883621013) := by
    rw [show ((655883621013 / 500000000000) : ℝ) = ((500000000000 / 655883621013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8836_neg : (136221379 / 500000000) ≤ -Real.log (125000000000 / 164146036097) ∧
    -Real.log (125000000000 / 164146036097) ≤ (272442759 / 1000000000) := by
  have h := checkLog_sound (w := (39146036097 / 289146036097)) (n := 12)
    (lo := (136221379 / 500000000)) (hi := (272442759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164146036097 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164146036097 / 125000000000) = 1/(125000000000 / 164146036097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8836 : Bounds (136221379 / 500000000) (272442759 / 1000000000) (Real.log (164146036097 / 125000000000)) := by
  have h := reflection_log_8836_neg
  have he : Real.log (164146036097 / 125000000000) = -Real.log (125000000000 / 164146036097) := by
    rw [show ((164146036097 / 125000000000) : ℝ) = ((125000000000 / 164146036097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8837_neg : (546184871 / 1000000000) ≤ -Real.log (5000000000 / 8633265167) ∧
    -Real.log (5000000000 / 8633265167) ≤ (68273109 / 125000000) := by
  have h := checkLog_sound (w := (3633265167 / 13633265167)) (n := 12)
    (lo := (546184871 / 1000000000)) (hi := (68273109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8633265167 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8633265167 / 5000000000) = 1/(5000000000 / 8633265167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8837 : Bounds (546184871 / 1000000000) (68273109 / 125000000) (Real.log (8633265167 / 5000000000)) := by
  have h := reflection_log_8837_neg
  have he : Real.log (8633265167 / 5000000000) = -Real.log (5000000000 / 8633265167) := by
    rw [show ((8633265167 / 5000000000) : ℝ) = ((5000000000 / 8633265167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8838_neg : (273630739 / 500000000) ≤ -Real.log (500000000000 / 864256480219) ∧
    -Real.log (500000000000 / 864256480219) ≤ (547261479 / 1000000000) := by
  have h := checkLog_sound (w := (364256480219 / 1364256480219)) (n := 12)
    (lo := (273630739 / 500000000)) (hi := (547261479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((864256480219 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(864256480219 / 500000000000) = 1/(500000000000 / 864256480219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8838 : Bounds (273630739 / 500000000) (547261479 / 1000000000) (Real.log (864256480219 / 500000000000)) := by
  have h := reflection_log_8838_neg
  have he : Real.log (864256480219 / 500000000000) = -Real.log (500000000000 / 864256480219) := by
    rw [show ((864256480219 / 500000000000) : ℝ) = ((500000000000 / 864256480219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8839_neg : (29630807 / 125000000) ≤ -Real.log (400 / 507) ∧
    -Real.log (400 / 507) ≤ (237046457 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 907)) (n := 12)
    (lo := (29630807 / 125000000)) (hi := (237046457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((507 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(507 / 400) = 1/(400 / 507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8839 : Bounds (29630807 / 125000000) (237046457 / 1000000000) (Real.log (507 / 400)) := by
  have h := reflection_log_8839_neg
  have he : Real.log (507 / 400) = -Real.log (400 / 507) := by
    rw [show ((507 / 400) : ℝ) = ((400 / 507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8840_neg : (155645969 / 500000000) ≤ -Real.log (293 / 400) ∧
    -Real.log (293 / 400) ≤ (311291939 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 693)) (n := 12)
    (lo := (155645969 / 500000000)) (hi := (311291939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 293) = 1/(293 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8840 : Bounds (-311291939 / 1000000000) (-155645969 / 500000000) (Real.log (293 / 400)) := by
  have h := reflection_log_8840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8841_neg : (33433 / 125000000) ≤ -Real.log (400000 / 400107) ∧
    -Real.log (400000 / 400107) ≤ (53493 / 200000000) := by
  have h := checkLog_sound (w := (107 / 800107)) (n := 12)
    (lo := (33433 / 125000000)) (hi := (53493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400107 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400107 / 400000) = 1/(400000 / 400107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8841 : Bounds (33433 / 125000000) (53493 / 200000000) (Real.log (400107 / 400000)) := by
  have h := reflection_log_8841_neg
  have he : Real.log (400107 / 400000) = -Real.log (400000 / 400107) := by
    rw [show ((400107 / 400000) : ℝ) = ((400000 / 400107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8842_neg : (53507 / 200000000) ≤ -Real.log (399893 / 400000) ∧
    -Real.log (399893 / 400000) ≤ (16721 / 62500000) := by
  have h := checkLog_sound (w := (107 / 799893)) (n := 12)
    (lo := (53507 / 200000000)) (hi := (16721 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399893) = 1/(399893 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8842 : Bounds (-16721 / 62500000) (-53507 / 200000000) (Real.log (399893 / 400000)) := by
  have h := reflection_log_8842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8843_neg : (126739253 / 1000000000) ≤ -Real.log (1000000 / 1135121) ∧
    -Real.log (1000000 / 1135121) ≤ (63369627 / 500000000) := by
  have h := checkLog_sound (w := (135121 / 2135121)) (n := 12)
    (lo := (126739253 / 1000000000)) (hi := (63369627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1135121 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1135121 / 1000000) = 1/(1000000 / 1135121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8843 : Bounds (126739253 / 1000000000) (63369627 / 500000000) (Real.log (1135121 / 1000000)) := by
  have h := reflection_log_8843_neg
  have he : Real.log (1135121 / 1000000) = -Real.log (1000000 / 1135121) := by
    rw [show ((1135121 / 1000000) : ℝ) = ((1000000 / 1135121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8844_neg : (72582833 / 500000000) ≤ -Real.log (864879 / 1000000) ∧
    -Real.log (864879 / 1000000) ≤ (145165667 / 1000000000) := by
  have h := checkLog_sound (w := (135121 / 1864879)) (n := 12)
    (lo := (72582833 / 500000000)) (hi := (145165667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 864879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 864879) = 1/(864879 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8844 : Bounds (-145165667 / 1000000000) (-72582833 / 500000000) (Real.log (864879 / 1000000)) := by
  have h := reflection_log_8844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8845_neg : (31800413 / 250000000) ≤ -Real.log (500000 / 567823) ∧
    -Real.log (500000 / 567823) ≤ (127201653 / 1000000000) := by
  have h := checkLog_sound (w := (67823 / 1067823)) (n := 12)
    (lo := (31800413 / 250000000)) (hi := (127201653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567823 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(567823 / 500000) = 1/(500000 / 567823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8845 : Bounds (31800413 / 250000000) (127201653 / 1000000000) (Real.log (567823 / 500000)) := by
  have h := reflection_log_8845_neg
  have he : Real.log (567823 / 500000) = -Real.log (500000 / 567823) := by
    rw [show ((567823 / 500000) : ℝ) = ((500000 / 567823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8846_neg : (145772871 / 1000000000) ≤ -Real.log (432177 / 500000) ∧
    -Real.log (432177 / 500000) ≤ (18221609 / 125000000) := by
  have h := checkLog_sound (w := (67823 / 932177)) (n := 12)
    (lo := (145772871 / 1000000000)) (hi := (18221609 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 432177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 432177) = 1/(432177 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8846 : Bounds (-18221609 / 125000000) (-145772871 / 1000000000) (Real.log (432177 / 500000)) := by
  have h := reflection_log_8846_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8847_neg : (18571219 / 1000000000) ≤ -Real.log (245400040671 / 250000000000) ∧
    -Real.log (245400040671 / 250000000000) ≤ (928561 / 50000000) := by
  have h := checkLog_sound (w := (4599959329 / 495400040671)) (n := 12)
    (lo := (18571219 / 1000000000)) (hi := (928561 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245400040671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245400040671) = 1/(245400040671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8847 : Bounds (-928561 / 50000000) (-18571219 / 1000000000) (Real.log (245400040671 / 250000000000)) := by
  have h := reflection_log_8847_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8848_neg : (18426413 / 1000000000) ≤ -Real.log (981742315359 / 1000000000000) ∧
    -Real.log (981742315359 / 1000000000000) ≤ (9213207 / 500000000) := by
  have h := checkLog_sound (w := (18257684641 / 1981742315359)) (n := 12)
    (lo := (18426413 / 1000000000)) (hi := (9213207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981742315359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981742315359) = 1/(981742315359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8848 : Bounds (-9213207 / 500000000) (-18426413 / 1000000000) (Real.log (981742315359 / 1000000000000)) := by
  have h := reflection_log_8848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8849_neg : (271904919 / 1000000000) ≤ -Real.log (500000000000 / 656231102847) ∧
    -Real.log (500000000000 / 656231102847) ≤ (6797623 / 25000000) := by
  have h := checkLog_sound (w := (156231102847 / 1156231102847)) (n := 12)
    (lo := (271904919 / 1000000000)) (hi := (6797623 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((656231102847 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(656231102847 / 500000000000) = 1/(500000000000 / 656231102847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8849 : Bounds (271904919 / 1000000000) (6797623 / 25000000) (Real.log (656231102847 / 500000000000)) := by
  have h := reflection_log_8849_neg
  have he : Real.log (656231102847 / 500000000000) = -Real.log (500000000000 / 656231102847) := by
    rw [show ((656231102847 / 500000000000) : ℝ) = ((500000000000 / 656231102847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8850_neg : (272974523 / 1000000000) ≤ -Real.log (50000000000 / 65693338609) ∧
    -Real.log (50000000000 / 65693338609) ≤ (68243631 / 250000000) := by
  have h := checkLog_sound (w := (15693338609 / 115693338609)) (n := 12)
    (lo := (272974523 / 1000000000)) (hi := (68243631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65693338609 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65693338609 / 50000000000) = 1/(50000000000 / 65693338609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8850 : Bounds (272974523 / 1000000000) (68243631 / 250000000) (Real.log (65693338609 / 50000000000)) := by
  have h := reflection_log_8850_neg
  have he : Real.log (65693338609 / 50000000000) = -Real.log (50000000000 / 65693338609) := by
    rw [show ((65693338609 / 50000000000) : ℝ) = ((50000000000 / 65693338609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8851_neg : (273630739 / 500000000) ≤ -Real.log (250000000000 / 432128240109) ∧
    -Real.log (250000000000 / 432128240109) ≤ (547261479 / 1000000000) := by
  have h := checkLog_sound (w := (182128240109 / 682128240109)) (n := 12)
    (lo := (273630739 / 500000000)) (hi := (547261479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432128240109 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(432128240109 / 250000000000) = 1/(250000000000 / 432128240109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8851 : Bounds (273630739 / 500000000) (547261479 / 1000000000) (Real.log (432128240109 / 250000000000)) := by
  have h := reflection_log_8851_neg
  have he : Real.log (432128240109 / 250000000000) = -Real.log (250000000000 / 432128240109) := by
    rw [show ((432128240109 / 250000000000) : ℝ) = ((250000000000 / 432128240109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8852_neg : (274169197 / 500000000) ≤ -Real.log (500000000000 / 865187713311) ∧
    -Real.log (500000000000 / 865187713311) ≤ (109667679 / 200000000) := by
  have h := checkLog_sound (w := (365187713311 / 1365187713311)) (n := 12)
    (lo := (274169197 / 500000000)) (hi := (109667679 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((865187713311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(865187713311 / 500000000000) = 1/(500000000000 / 865187713311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8852 : Bounds (274169197 / 500000000) (109667679 / 200000000) (Real.log (865187713311 / 500000000000)) := by
  have h := reflection_log_8852_neg
  have he : Real.log (865187713311 / 500000000000) = -Real.log (500000000000 / 865187713311) := by
    rw [show ((865187713311 / 500000000000) : ℝ) = ((500000000000 / 865187713311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8853_neg : (29680107 / 125000000) ≤ -Real.log (250 / 317) ∧
    -Real.log (250 / 317) ≤ (237440857 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 567)) (n := 12)
    (lo := (29680107 / 125000000)) (hi := (237440857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317 / 250) = 1/(250 / 317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8853 : Bounds (29680107 / 125000000) (237440857 / 1000000000) (Real.log (317 / 250)) := by
  have h := reflection_log_8853_neg
  have he : Real.log (317 / 250) = -Real.log (250 / 317) := by
    rw [show ((317 / 250) : ℝ) = ((250 / 317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8854_neg : (62394953 / 200000000) ≤ -Real.log (183 / 250) ∧
    -Real.log (183 / 250) ≤ (155987383 / 500000000) := by
  have h := checkLog_sound (w := (67 / 433)) (n := 12)
    (lo := (62394953 / 200000000)) (hi := (155987383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 183) = 1/(183 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8854 : Bounds (-155987383 / 500000000) (-62394953 / 200000000) (Real.log (183 / 250)) := by
  have h := reflection_log_8854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8855_neg : (66991 / 250000000) ≤ -Real.log (250000 / 250067) ∧
    -Real.log (250000 / 250067) ≤ (53593 / 200000000) := by
  have h := checkLog_sound (w := (67 / 500067)) (n := 12)
    (lo := (66991 / 250000000)) (hi := (53593 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250067 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250067 / 250000) = 1/(250000 / 250067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8855 : Bounds (66991 / 250000000) (53593 / 200000000) (Real.log (250067 / 250000)) := by
  have h := reflection_log_8855_neg
  have he : Real.log (250067 / 250000) = -Real.log (250000 / 250067) := by
    rw [show ((250067 / 250000) : ℝ) = ((250000 / 250067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8856_neg : (53607 / 200000000) ≤ -Real.log (249933 / 250000) ∧
    -Real.log (249933 / 250000) ≤ (67009 / 250000000) := by
  have h := checkLog_sound (w := (67 / 499933)) (n := 12)
    (lo := (53607 / 200000000)) (hi := (67009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249933) = 1/(249933 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8856 : Bounds (-67009 / 250000000) (-53607 / 200000000) (Real.log (249933 / 250000)) := by
  have h := reflection_log_8856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8857_neg : (126968277 / 1000000000) ≤ -Real.log (1000000 / 1135381) ∧
    -Real.log (1000000 / 1135381) ≤ (63484139 / 500000000) := by
  have h := checkLog_sound (w := (135381 / 2135381)) (n := 12)
    (lo := (126968277 / 1000000000)) (hi := (63484139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1135381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1135381 / 1000000) = 1/(1000000 / 1135381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8857 : Bounds (126968277 / 1000000000) (63484139 / 500000000) (Real.log (1135381 / 1000000)) := by
  have h := reflection_log_8857_neg
  have he : Real.log (1135381 / 1000000) = -Real.log (1000000 / 1135381) := by
    rw [show ((1135381 / 1000000) : ℝ) = ((1000000 / 1135381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8858_neg : (145466331 / 1000000000) ≤ -Real.log (864619 / 1000000) ∧
    -Real.log (864619 / 1000000) ≤ (36366583 / 250000000) := by
  have h := checkLog_sound (w := (135381 / 1864619)) (n := 12)
    (lo := (145466331 / 1000000000)) (hi := (36366583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 864619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 864619) = 1/(864619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8858 : Bounds (-36366583 / 250000000) (-145466331 / 1000000000) (Real.log (864619 / 1000000)) := by
  have h := reflection_log_8858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8859_neg : (12743057 / 100000000) ≤ -Real.log (500000 / 567953) ∧
    -Real.log (500000 / 567953) ≤ (127430571 / 1000000000) := by
  have h := checkLog_sound (w := (67953 / 1067953)) (n := 12)
    (lo := (12743057 / 100000000)) (hi := (127430571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((567953 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(567953 / 500000) = 1/(500000 / 567953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8859 : Bounds (12743057 / 100000000) (127430571 / 1000000000) (Real.log (567953 / 500000)) := by
  have h := reflection_log_8859_neg
  have he : Real.log (567953 / 500000) = -Real.log (500000 / 567953) := by
    rw [show ((567953 / 500000) : ℝ) = ((500000 / 567953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8860_neg : (146073719 / 1000000000) ≤ -Real.log (432047 / 500000) ∧
    -Real.log (432047 / 500000) ≤ (3651843 / 25000000) := by
  have h := checkLog_sound (w := (67953 / 932047)) (n := 12)
    (lo := (146073719 / 1000000000)) (hi := (3651843 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 432047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 432047) = 1/(432047 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8860 : Bounds (-3651843 / 25000000) (-146073719 / 1000000000) (Real.log (432047 / 500000)) := by
  have h := reflection_log_8860_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8861_neg : (18643149 / 1000000000) ≤ -Real.log (245382389791 / 250000000000) ∧
    -Real.log (245382389791 / 250000000000) ≤ (372863 / 20000000) := by
  have h := checkLog_sound (w := (4617610209 / 495382389791)) (n := 12)
    (lo := (18643149 / 1000000000)) (hi := (372863 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245382389791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245382389791) = 1/(245382389791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8861 : Bounds (-372863 / 20000000) (-18643149 / 1000000000) (Real.log (245382389791 / 250000000000)) := by
  have h := reflection_log_8861_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8862_neg : (9249027 / 500000000) ≤ -Real.log (981671984839 / 1000000000000) ∧
    -Real.log (981671984839 / 1000000000000) ≤ (3699611 / 200000000) := by
  have h := checkLog_sound (w := (18328015161 / 1981671984839)) (n := 12)
    (lo := (9249027 / 500000000)) (hi := (3699611 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981671984839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981671984839) = 1/(981671984839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8862 : Bounds (-3699611 / 200000000) (-9249027 / 500000000) (Real.log (981671984839 / 1000000000000)) := by
  have h := reflection_log_8862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8863_neg : (17027163 / 62500000) ≤ -Real.log (100000000000 / 131315758733) ∧
    -Real.log (100000000000 / 131315758733) ≤ (272434609 / 1000000000) := by
  have h := checkLog_sound (w := (31315758733 / 231315758733)) (n := 12)
    (lo := (17027163 / 62500000)) (hi := (272434609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131315758733 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131315758733 / 100000000000) = 1/(100000000000 / 131315758733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8863 : Bounds (17027163 / 62500000) (272434609 / 1000000000) (Real.log (131315758733 / 100000000000)) := by
  have h := reflection_log_8863_neg
  have he : Real.log (131315758733 / 100000000000) = -Real.log (100000000000 / 131315758733) := by
    rw [show ((131315758733 / 100000000000) : ℝ) = ((100000000000 / 131315758733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8864_neg : (27350429 / 100000000) ≤ -Real.log (500000000000 / 657281499467) ∧
    -Real.log (500000000000 / 657281499467) ≤ (273504291 / 1000000000) := by
  have h := checkLog_sound (w := (157281499467 / 1157281499467)) (n := 12)
    (lo := (27350429 / 100000000)) (hi := (273504291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657281499467 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657281499467 / 500000000000) = 1/(500000000000 / 657281499467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8864 : Bounds (27350429 / 100000000) (273504291 / 1000000000) (Real.log (657281499467 / 500000000000)) := by
  have h := reflection_log_8864_neg
  have he : Real.log (657281499467 / 500000000000) = -Real.log (500000000000 / 657281499467) := by
    rw [show ((657281499467 / 500000000000) : ℝ) = ((500000000000 / 657281499467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8865_neg : (274169197 / 500000000) ≤ -Real.log (50000000000 / 86518771331) ∧
    -Real.log (50000000000 / 86518771331) ≤ (109667679 / 200000000) := by
  have h := checkLog_sound (w := (36518771331 / 136518771331)) (n := 12)
    (lo := (274169197 / 500000000)) (hi := (109667679 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86518771331 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86518771331 / 50000000000) = 1/(50000000000 / 86518771331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8865 : Bounds (274169197 / 500000000) (109667679 / 200000000) (Real.log (86518771331 / 50000000000)) := by
  have h := reflection_log_8865_neg
  have he : Real.log (86518771331 / 50000000000) = -Real.log (50000000000 / 86518771331) := by
    rw [show ((86518771331 / 50000000000) : ℝ) = ((50000000000 / 86518771331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8866_neg : (549415621 / 1000000000) ≤ -Real.log (25000000000 / 43306010929) ∧
    -Real.log (25000000000 / 43306010929) ≤ (274707811 / 500000000) := by
  have h := checkLog_sound (w := (18306010929 / 68306010929)) (n := 12)
    (lo := (549415621 / 1000000000)) (hi := (274707811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43306010929 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43306010929 / 25000000000) = 1/(25000000000 / 43306010929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8866 : Bounds (549415621 / 1000000000) (274707811 / 500000000) (Real.log (43306010929 / 25000000000)) := by
  have h := reflection_log_8866_neg
  have he : Real.log (43306010929 / 25000000000) = -Real.log (25000000000 / 43306010929) := by
    rw [show ((43306010929 / 25000000000) : ℝ) = ((25000000000 / 43306010929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8867_neg : (2378351 / 10000000) ≤ -Real.log (2000 / 2537) ∧
    -Real.log (2000 / 2537) ≤ (237835101 / 1000000000) := by
  have h := checkLog_sound (w := (537 / 4537)) (n := 12)
    (lo := (2378351 / 10000000)) (hi := (237835101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2537 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2537 / 2000) = 1/(2000 / 2537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8867 : Bounds (2378351 / 10000000) (237835101 / 1000000000) (Real.log (2537 / 2000)) := by
  have h := reflection_log_8867_neg
  have he : Real.log (2537 / 2000) = -Real.log (2000 / 2537) := by
    rw [show ((2537 / 2000) : ℝ) = ((2000 / 2537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8868_neg : (156329029 / 500000000) ≤ -Real.log (1463 / 2000) ∧
    -Real.log (1463 / 2000) ≤ (312658059 / 1000000000) := by
  have h := checkLog_sound (w := (537 / 3463)) (n := 12)
    (lo := (156329029 / 500000000)) (hi := (312658059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1463) = 1/(1463 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8868 : Bounds (-312658059 / 1000000000) (-156329029 / 500000000) (Real.log (1463 / 2000)) := by
  have h := reflection_log_8868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8869_neg : (268463 / 1000000000) ≤ -Real.log (2000000 / 2000537) ∧
    -Real.log (2000000 / 2000537) ≤ (16779 / 62500000) := by
  have h := checkLog_sound (w := (537 / 4000537)) (n := 12)
    (lo := (268463 / 1000000000)) (hi := (16779 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000537 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000537 / 2000000) = 1/(2000000 / 2000537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8869 : Bounds (268463 / 1000000000) (16779 / 62500000) (Real.log (2000537 / 2000000)) := by
  have h := reflection_log_8869_neg
  have he : Real.log (2000537 / 2000000) = -Real.log (2000000 / 2000537) := by
    rw [show ((2000537 / 2000000) : ℝ) = ((2000000 / 2000537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8870_neg : (33567 / 125000000) ≤ -Real.log (1999463 / 2000000) ∧
    -Real.log (1999463 / 2000000) ≤ (268537 / 1000000000) := by
  have h := checkLog_sound (w := (537 / 3999463)) (n := 12)
    (lo := (33567 / 125000000)) (hi := (268537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999463) = 1/(1999463 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8870 : Bounds (-268537 / 1000000000) (-33567 / 125000000) (Real.log (1999463 / 2000000)) := by
  have h := reflection_log_8870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8871_neg : (7949773 / 62500000) ≤ -Real.log (25000 / 28391) ∧
    -Real.log (25000 / 28391) ≤ (127196369 / 1000000000) := by
  have h := checkLog_sound (w := (3391 / 53391)) (n := 12)
    (lo := (7949773 / 62500000)) (hi := (127196369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28391 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28391 / 25000) = 1/(25000 / 28391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8871 : Bounds (7949773 / 62500000) (127196369 / 1000000000) (Real.log (28391 / 25000)) := by
  have h := reflection_log_8871_neg
  have he : Real.log (28391 / 25000) = -Real.log (25000 / 28391) := by
    rw [show ((28391 / 25000) : ℝ) = ((25000 / 28391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8872_neg : (14576593 / 100000000) ≤ -Real.log (21609 / 25000) ∧
    -Real.log (21609 / 25000) ≤ (145765931 / 1000000000) := by
  have h := checkLog_sound (w := (3391 / 46609)) (n := 12)
    (lo := (14576593 / 100000000)) (hi := (145765931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 21609) = 1/(21609 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8872 : Bounds (-145765931 / 1000000000) (-14576593 / 100000000) (Real.log (21609 / 25000)) := by
  have h := reflection_log_8872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8873_neg : (31914859 / 250000000) ≤ -Real.log (500000 / 568083) ∧
    -Real.log (500000 / 568083) ≤ (127659437 / 1000000000) := by
  have h := checkLog_sound (w := (68083 / 1068083)) (n := 12)
    (lo := (31914859 / 250000000)) (hi := (127659437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((568083 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(568083 / 500000) = 1/(500000 / 568083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8873 : Bounds (31914859 / 250000000) (127659437 / 1000000000) (Real.log (568083 / 500000)) := by
  have h := reflection_log_8873_neg
  have he : Real.log (568083 / 500000) = -Real.log (500000 / 568083) := by
    rw [show ((568083 / 500000) : ℝ) = ((500000 / 568083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8874_neg : (73187329 / 500000000) ≤ -Real.log (431917 / 500000) ∧
    -Real.log (431917 / 500000) ≤ (146374659 / 1000000000) := by
  have h := checkLog_sound (w := (68083 / 931917)) (n := 12)
    (lo := (73187329 / 500000000)) (hi := (146374659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 431917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 431917) = 1/(431917 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8874 : Bounds (-146374659 / 1000000000) (-73187329 / 500000000) (Real.log (431917 / 500000)) := by
  have h := reflection_log_8874_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8875_neg : (18715221 / 1000000000) ≤ -Real.log (245364705111 / 250000000000) ∧
    -Real.log (245364705111 / 250000000000) ≤ (9357611 / 500000000) := by
  have h := checkLog_sound (w := (4635294889 / 495364705111)) (n := 12)
    (lo := (18715221 / 1000000000)) (hi := (9357611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245364705111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245364705111) = 1/(245364705111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8875 : Bounds (-9357611 / 500000000) (-18715221 / 1000000000) (Real.log (245364705111 / 250000000000)) := by
  have h := reflection_log_8875_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8876_neg : (18569561 / 1000000000) ≤ -Real.log (613501119 / 625000000) ∧
    -Real.log (613501119 / 625000000) ≤ (9284781 / 500000000) := by
  have h := checkLog_sound (w := (11498881 / 1238501119)) (n := 12)
    (lo := (18569561 / 1000000000)) (hi := (9284781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 613501119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 613501119) = 1/(613501119 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8876 : Bounds (-9284781 / 500000000) (-18569561 / 1000000000) (Real.log (613501119 / 625000000)) := by
  have h := reflection_log_8876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8877_neg : (136481149 / 500000000) ≤ -Real.log (62500000000 / 82115669397) ∧
    -Real.log (62500000000 / 82115669397) ≤ (272962299 / 1000000000) := by
  have h := checkLog_sound (w := (19615669397 / 144615669397)) (n := 12)
    (lo := (136481149 / 500000000)) (hi := (272962299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82115669397 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82115669397 / 62500000000) = 1/(62500000000 / 82115669397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8877 : Bounds (136481149 / 500000000) (272962299 / 1000000000) (Real.log (82115669397 / 62500000000)) := by
  have h := reflection_log_8877_neg
  have he : Real.log (82115669397 / 62500000000) = -Real.log (62500000000 / 82115669397) := by
    rw [show ((82115669397 / 62500000000) : ℝ) = ((62500000000 / 82115669397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8878_neg : (137017047 / 500000000) ≤ -Real.log (500000000000 / 657629822397) ∧
    -Real.log (500000000000 / 657629822397) ≤ (54806819 / 200000000) := by
  have h := checkLog_sound (w := (157629822397 / 1157629822397)) (n := 12)
    (lo := (137017047 / 500000000)) (hi := (54806819 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657629822397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657629822397 / 500000000000) = 1/(500000000000 / 657629822397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8878 : Bounds (137017047 / 500000000) (54806819 / 200000000) (Real.log (657629822397 / 500000000000)) := by
  have h := reflection_log_8878_neg
  have he : Real.log (657629822397 / 500000000000) = -Real.log (500000000000 / 657629822397) := by
    rw [show ((657629822397 / 500000000000) : ℝ) = ((500000000000 / 657629822397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8879_neg : (549415621 / 1000000000) ≤ -Real.log (500000000000 / 866120218579) ∧
    -Real.log (500000000000 / 866120218579) ≤ (274707811 / 500000000) := by
  have h := checkLog_sound (w := (366120218579 / 1366120218579)) (n := 12)
    (lo := (549415621 / 1000000000)) (hi := (274707811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((866120218579 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(866120218579 / 500000000000) = 1/(500000000000 / 866120218579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8879 : Bounds (549415621 / 1000000000) (274707811 / 500000000) (Real.log (866120218579 / 500000000000)) := by
  have h := reflection_log_8879_neg
  have he : Real.log (866120218579 / 500000000000) = -Real.log (500000000000 / 866120218579) := by
    rw [show ((866120218579 / 500000000000) : ℝ) = ((500000000000 / 866120218579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8880_neg : (275246579 / 500000000) ≤ -Real.log (500000000000 / 867053998633) ∧
    -Real.log (500000000000 / 867053998633) ≤ (550493159 / 1000000000) := by
  have h := checkLog_sound (w := (367053998633 / 1367053998633)) (n := 12)
    (lo := (275246579 / 500000000)) (hi := (550493159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((867053998633 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(867053998633 / 500000000000) = 1/(500000000000 / 867053998633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8880 : Bounds (275246579 / 500000000) (550493159 / 1000000000) (Real.log (867053998633 / 500000000000)) := by
  have h := reflection_log_8880_neg
  have he : Real.log (867053998633 / 500000000000) = -Real.log (500000000000 / 867053998633) := by
    rw [show ((867053998633 / 500000000000) : ℝ) = ((500000000000 / 867053998633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8881_neg : (59557297 / 250000000) ≤ -Real.log (1000 / 1269) ∧
    -Real.log (1000 / 1269) ≤ (238229189 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 2269)) (n := 12)
    (lo := (59557297 / 250000000)) (hi := (238229189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1269 / 1000) = 1/(1000 / 1269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8881 : Bounds (59557297 / 250000000) (238229189 / 1000000000) (Real.log (1269 / 1000)) := by
  have h := reflection_log_8881_neg
  have he : Real.log (1269 / 1000) = -Real.log (1000 / 1269) := by
    rw [show ((1269 / 1000) : ℝ) = ((1000 / 1269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8882_neg : (313341819 / 1000000000) ≤ -Real.log (731 / 1000) ∧
    -Real.log (731 / 1000) ≤ (15667091 / 50000000) := by
  have h := checkLog_sound (w := (269 / 1731)) (n := 12)
    (lo := (313341819 / 1000000000)) (hi := (15667091 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 731) = 1/(731 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8882 : Bounds (-15667091 / 50000000) (-313341819 / 1000000000) (Real.log (731 / 1000)) := by
  have h := reflection_log_8882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8883_neg : (268963 / 1000000000) ≤ -Real.log (1000000 / 1000269) ∧
    -Real.log (1000000 / 1000269) ≤ (67241 / 250000000) := by
  have h := checkLog_sound (w := (269 / 2000269)) (n := 12)
    (lo := (268963 / 1000000000)) (hi := (67241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000269 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000269 / 1000000) = 1/(1000000 / 1000269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8883 : Bounds (268963 / 1000000000) (67241 / 250000000) (Real.log (1000269 / 1000000)) := by
  have h := reflection_log_8883_neg
  have he : Real.log (1000269 / 1000000) = -Real.log (1000000 / 1000269) := by
    rw [show ((1000269 / 1000000) : ℝ) = ((1000000 / 1000269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8884_neg : (67259 / 250000000) ≤ -Real.log (999731 / 1000000) ∧
    -Real.log (999731 / 1000000) ≤ (269037 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 1999731)) (n := 12)
    (lo := (67259 / 250000000)) (hi := (269037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999731) = 1/(999731 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8884 : Bounds (-269037 / 1000000000) (-67259 / 250000000) (Real.log (999731 / 1000000)) := by
  have h := reflection_log_8884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8885_neg : (15928161 / 125000000) ≤ -Real.log (10000 / 11359) ∧
    -Real.log (10000 / 11359) ≤ (127425289 / 1000000000) := by
  have h := checkLog_sound (w := (1359 / 21359)) (n := 12)
    (lo := (15928161 / 125000000)) (hi := (127425289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11359 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11359 / 10000) = 1/(10000 / 11359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8885 : Bounds (15928161 / 125000000) (127425289 / 1000000000) (Real.log (11359 / 10000)) := by
  have h := reflection_log_8885_neg
  have he : Real.log (11359 / 10000) = -Real.log (10000 / 11359) := by
    rw [show ((11359 / 10000) : ℝ) = ((10000 / 11359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8886_neg : (18258347 / 125000000) ≤ -Real.log (8641 / 10000) ∧
    -Real.log (8641 / 10000) ≤ (146066777 / 1000000000) := by
  have h := checkLog_sound (w := (1359 / 18641)) (n := 12)
    (lo := (18258347 / 125000000)) (hi := (146066777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8641) = 1/(8641 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8886 : Bounds (-146066777 / 1000000000) (-18258347 / 125000000) (Real.log (8641 / 10000)) := by
  have h := reflection_log_8886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8887_neg : (127889129 / 1000000000) ≤ -Real.log (1000000 / 1136427) ∧
    -Real.log (1000000 / 1136427) ≤ (12788913 / 100000000) := by
  have h := checkLog_sound (w := (136427 / 2136427)) (n := 12)
    (lo := (127889129 / 1000000000)) (hi := (12788913 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136427 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1136427 / 1000000) = 1/(1000000 / 1136427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8887 : Bounds (127889129 / 1000000000) (12788913 / 100000000) (Real.log (1136427 / 1000000)) := by
  have h := reflection_log_8887_neg
  have he : Real.log (1136427 / 1000000) = -Real.log (1000000 / 1136427) := by
    rw [show ((1136427 / 1000000) : ℝ) = ((1000000 / 1136427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8888_neg : (29335369 / 200000000) ≤ -Real.log (863573 / 1000000) ∧
    -Real.log (863573 / 1000000) ≤ (73338423 / 500000000) := by
  have h := checkLog_sound (w := (136427 / 1863573)) (n := 12)
    (lo := (29335369 / 200000000)) (hi := (73338423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 863573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 863573) = 1/(863573 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8888 : Bounds (-73338423 / 500000000) (-29335369 / 200000000) (Real.log (863573 / 1000000)) := by
  have h := reflection_log_8888_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8889_neg : (3757543 / 200000000) ≤ -Real.log (981387673671 / 1000000000000) ∧
    -Real.log (981387673671 / 1000000000000) ≤ (4696929 / 250000000) := by
  have h := checkLog_sound (w := (18612326329 / 1981387673671)) (n := 12)
    (lo := (3757543 / 200000000)) (hi := (4696929 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981387673671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981387673671) = 1/(981387673671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8889 : Bounds (-4696929 / 250000000) (-3757543 / 200000000) (Real.log (981387673671 / 1000000000000)) := by
  have h := reflection_log_8889_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8890_neg : (18641487 / 1000000000) ≤ -Real.log (98153119 / 100000000) ∧
    -Real.log (98153119 / 100000000) ≤ (1165093 / 62500000) := by
  have h := checkLog_sound (w := (1846881 / 198153119)) (n := 12)
    (lo := (18641487 / 1000000000)) (hi := (1165093 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 98153119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 98153119) = 1/(98153119 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8890 : Bounds (-1165093 / 62500000) (-18641487 / 1000000000) (Real.log (98153119 / 100000000)) := by
  have h := reflection_log_8890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8891_neg : (8546627 / 31250000) ≤ -Real.log (500000000000 / 657273463719) ∧
    -Real.log (500000000000 / 657273463719) ≤ (54698413 / 200000000) := by
  have h := checkLog_sound (w := (157273463719 / 1157273463719)) (n := 12)
    (lo := (8546627 / 31250000)) (hi := (54698413 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657273463719 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657273463719 / 500000000000) = 1/(500000000000 / 657273463719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8891 : Bounds (8546627 / 31250000) (54698413 / 200000000) (Real.log (657273463719 / 500000000000)) := by
  have h := reflection_log_8891_neg
  have he : Real.log (657273463719 / 500000000000) = -Real.log (500000000000 / 657273463719) := by
    rw [show ((657273463719 / 500000000000) : ℝ) = ((500000000000 / 657273463719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8892_neg : (10982639 / 40000000) ≤ -Real.log (100000000000 / 131595939197) ∧
    -Real.log (100000000000 / 131595939197) ≤ (34320747 / 125000000) := by
  have h := checkLog_sound (w := (31595939197 / 231595939197)) (n := 12)
    (lo := (10982639 / 40000000)) (hi := (34320747 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131595939197 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131595939197 / 100000000000) = 1/(100000000000 / 131595939197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8892 : Bounds (10982639 / 40000000) (34320747 / 125000000) (Real.log (131595939197 / 100000000000)) := by
  have h := reflection_log_8892_neg
  have he : Real.log (131595939197 / 100000000000) = -Real.log (100000000000 / 131595939197) := by
    rw [show ((131595939197 / 100000000000) : ℝ) = ((100000000000 / 131595939197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8893_neg : (275246579 / 500000000) ≤ -Real.log (62500000000 / 108381749829) ∧
    -Real.log (62500000000 / 108381749829) ≤ (550493159 / 1000000000) := by
  have h := checkLog_sound (w := (45881749829 / 170881749829)) (n := 12)
    (lo := (275246579 / 500000000)) (hi := (550493159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108381749829 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108381749829 / 62500000000) = 1/(62500000000 / 108381749829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8893 : Bounds (275246579 / 500000000) (550493159 / 1000000000) (Real.log (108381749829 / 62500000000)) := by
  have h := reflection_log_8893_neg
  have he : Real.log (108381749829 / 62500000000) = -Real.log (62500000000 / 108381749829) := by
    rw [show ((108381749829 / 62500000000) : ℝ) = ((62500000000 / 108381749829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8894_neg : (551571007 / 1000000000) ≤ -Real.log (62500000000 / 108498632011) ∧
    -Real.log (62500000000 / 108498632011) ≤ (8618297 / 15625000) := by
  have h := checkLog_sound (w := (45998632011 / 170998632011)) (n := 12)
    (lo := (551571007 / 1000000000)) (hi := (8618297 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108498632011 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108498632011 / 62500000000) = 1/(62500000000 / 108498632011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8894 : Bounds (551571007 / 1000000000) (8618297 / 15625000) (Real.log (108498632011 / 62500000000)) := by
  have h := reflection_log_8894_neg
  have he : Real.log (108498632011 / 62500000000) = -Real.log (62500000000 / 108498632011) := by
    rw [show ((108498632011 / 62500000000) : ℝ) = ((62500000000 / 108498632011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8895_neg : (119311561 / 500000000) ≤ -Real.log (2000 / 2539) ∧
    -Real.log (2000 / 2539) ≤ (238623123 / 1000000000) := by
  have h := checkLog_sound (w := (539 / 4539)) (n := 12)
    (lo := (119311561 / 500000000)) (hi := (238623123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2539 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2539 / 2000) = 1/(2000 / 2539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8895 : Bounds (119311561 / 500000000) (238623123 / 1000000000) (Real.log (2539 / 2000)) := by
  have h := reflection_log_8895_neg
  have he : Real.log (2539 / 2000) = -Real.log (2000 / 2539) := by
    rw [show ((2539 / 2000) : ℝ) = ((2000 / 2539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
