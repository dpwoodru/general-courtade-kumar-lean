import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2816_neg : (85207 / 500000000) ≤ -Real.log (1249787 / 1250000) ∧
    -Real.log (1249787 / 1250000) ≤ (34083 / 200000000) := by
  have h := checkLog_sound (w := (213 / 2499787)) (n := 12)
    (lo := (85207 / 500000000)) (hi := (34083 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249787) = 1/(1249787 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2816 : Bounds (-34083 / 200000000) (-85207 / 500000000) (Real.log (1249787 / 1250000)) := by
  have h := reflection_log_2816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2817_neg : (82053607 / 1000000000) ≤ -Real.log (500000 / 542757) ∧
    -Real.log (500000 / 542757) ≤ (10256701 / 125000000) := by
  have h := checkLog_sound (w := (42757 / 1042757)) (n := 12)
    (lo := (82053607 / 1000000000)) (hi := (10256701 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542757 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542757 / 500000) = 1/(500000 / 542757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2817 : Bounds (82053607 / 1000000000) (10256701 / 125000000) (Real.log (542757 / 500000)) := by
  have h := reflection_log_2817_neg
  have he : Real.log (542757 / 500000) = -Real.log (500000 / 542757) := by
    rw [show ((542757 / 500000) : ℝ) = ((500000 / 542757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2818_neg : (558707 / 6250000) ≤ -Real.log (457243 / 500000) ∧
    -Real.log (457243 / 500000) ≤ (89393121 / 1000000000) := by
  have h := checkLog_sound (w := (42757 / 957243)) (n := 12)
    (lo := (558707 / 6250000)) (hi := (89393121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457243) = 1/(457243 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2818 : Bounds (-89393121 / 1000000000) (-558707 / 6250000) (Real.log (457243 / 500000)) := by
  have h := reflection_log_2818_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2819_neg : (82257177 / 1000000000) ≤ -Real.log (200000 / 217147) ∧
    -Real.log (200000 / 217147) ≤ (41128589 / 500000000) := by
  have h := checkLog_sound (w := (17147 / 417147)) (n := 12)
    (lo := (82257177 / 1000000000)) (hi := (41128589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217147 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217147 / 200000) = 1/(200000 / 217147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2819 : Bounds (82257177 / 1000000000) (41128589 / 500000000) (Real.log (217147 / 200000)) := by
  have h := reflection_log_2819_neg
  have he : Real.log (217147 / 200000) = -Real.log (200000 / 217147) := by
    rw [show ((217147 / 200000) : ℝ) = ((200000 / 217147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2820_neg : (17926963 / 200000000) ≤ -Real.log (182853 / 200000) ∧
    -Real.log (182853 / 200000) ≤ (175068 / 1953125) := by
  have h := checkLog_sound (w := (17147 / 382853)) (n := 12)
    (lo := (17926963 / 200000000)) (hi := (175068 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182853) = 1/(182853 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2820 : Bounds (-175068 / 1953125) (-17926963 / 200000000) (Real.log (182853 / 200000)) := by
  have h := reflection_log_2820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2821_neg : (3688819 / 500000000) ≤ -Real.log (39705980391 / 40000000000) ∧
    -Real.log (39705980391 / 40000000000) ≤ (7377639 / 1000000000) := by
  have h := checkLog_sound (w := (294019609 / 79705980391)) (n := 12)
    (lo := (3688819 / 500000000)) (hi := (7377639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39705980391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39705980391) = 1/(39705980391 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2821 : Bounds (-7377639 / 1000000000) (-3688819 / 500000000) (Real.log (39705980391 / 40000000000)) := by
  have h := reflection_log_2821_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2822_neg : (917439 / 125000000) ≤ -Real.log (248171838951 / 250000000000) ∧
    -Real.log (248171838951 / 250000000000) ≤ (7339513 / 1000000000) := by
  have h := checkLog_sound (w := (1828161049 / 498171838951)) (n := 12)
    (lo := (917439 / 125000000)) (hi := (7339513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248171838951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248171838951) = 1/(248171838951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2822 : Bounds (-7339513 / 1000000000) (-917439 / 125000000) (Real.log (248171838951 / 250000000000)) := by
  have h := reflection_log_2822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2823_neg : (171446727 / 1000000000) ≤ -Real.log (250000000000 / 296755226433) ∧
    -Real.log (250000000000 / 296755226433) ≤ (21430841 / 125000000) := by
  have h := checkLog_sound (w := (46755226433 / 546755226433)) (n := 12)
    (lo := (171446727 / 1000000000)) (hi := (21430841 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296755226433 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296755226433 / 250000000000) = 1/(250000000000 / 296755226433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2823 : Bounds (171446727 / 1000000000) (21430841 / 125000000) (Real.log (296755226433 / 250000000000)) := by
  have h := reflection_log_2823_neg
  have he : Real.log (296755226433 / 250000000000) = -Real.log (250000000000 / 296755226433) := by
    rw [show ((296755226433 / 250000000000) : ℝ) = ((250000000000 / 296755226433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2824_neg : (21486499 / 125000000) ≤ -Real.log (100000000000 / 118754956167) ∧
    -Real.log (100000000000 / 118754956167) ≤ (171891993 / 1000000000) := by
  have h := checkLog_sound (w := (18754956167 / 218754956167)) (n := 12)
    (lo := (21486499 / 125000000)) (hi := (171891993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118754956167 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118754956167 / 100000000000) = 1/(100000000000 / 118754956167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2824 : Bounds (21486499 / 125000000) (171891993 / 1000000000) (Real.log (118754956167 / 100000000000)) := by
  have h := reflection_log_2824_neg
  have he : Real.log (118754956167 / 100000000000) = -Real.log (100000000000 / 118754956167) := by
    rw [show ((118754956167 / 100000000000) : ℝ) = ((100000000000 / 118754956167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2825_neg : (68790243 / 200000000) ≤ -Real.log (500000000000 / 705254911413) ∧
    -Real.log (500000000000 / 705254911413) ≤ (21496951 / 62500000) := by
  have h := checkLog_sound (w := (205254911413 / 1205254911413)) (n := 12)
    (lo := (68790243 / 200000000)) (hi := (21496951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705254911413 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705254911413 / 500000000000) = 1/(500000000000 / 705254911413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2825 : Bounds (68790243 / 200000000) (21496951 / 62500000) (Real.log (705254911413 / 500000000000)) := by
  have h := reflection_log_2825_neg
  have he : Real.log (705254911413 / 500000000000) = -Real.log (500000000000 / 705254911413) := by
    rw [show ((705254911413 / 500000000000) : ℝ) = ((500000000000 / 705254911413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2826_neg : (43019649 / 125000000) ≤ -Real.log (100000000000 / 141080038573) ∧
    -Real.log (100000000000 / 141080038573) ≤ (344157193 / 1000000000) := by
  have h := checkLog_sound (w := (41080038573 / 241080038573)) (n := 12)
    (lo := (43019649 / 125000000)) (hi := (344157193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141080038573 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141080038573 / 100000000000) = 1/(100000000000 / 141080038573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2826 : Bounds (43019649 / 125000000) (344157193 / 1000000000) (Real.log (141080038573 / 100000000000)) := by
  have h := reflection_log_2826_neg
  have he : Real.log (141080038573 / 100000000000) = -Real.log (100000000000 / 141080038573) := by
    rw [show ((141080038573 / 100000000000) : ℝ) = ((100000000000 / 141080038573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2827_neg : (157431007 / 1000000000) ≤ -Real.log (2000 / 2341) ∧
    -Real.log (2000 / 2341) ≤ (4919719 / 31250000) := by
  have h := checkLog_sound (w := (341 / 4341)) (n := 12)
    (lo := (157431007 / 1000000000)) (hi := (4919719 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2341 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2341 / 2000) = 1/(2000 / 2341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2827 : Bounds (157431007 / 1000000000) (4919719 / 31250000) (Real.log (2341 / 2000)) := by
  have h := reflection_log_2827_neg
  have he : Real.log (2341 / 2000) = -Real.log (2000 / 2341) := by
    rw [show ((2341 / 2000) : ℝ) = ((2000 / 2341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2828_neg : (186932169 / 1000000000) ≤ -Real.log (1659 / 2000) ∧
    -Real.log (1659 / 2000) ≤ (18693217 / 100000000) := by
  have h := checkLog_sound (w := (341 / 3659)) (n := 12)
    (lo := (186932169 / 1000000000)) (hi := (18693217 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1659) = 1/(1659 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2828 : Bounds (-18693217 / 100000000) (-186932169 / 1000000000) (Real.log (1659 / 2000)) := by
  have h := reflection_log_2828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2829_neg : (34097 / 200000000) ≤ -Real.log (2000000 / 2000341) ∧
    -Real.log (2000000 / 2000341) ≤ (85243 / 500000000) := by
  have h := checkLog_sound (w := (341 / 4000341)) (n := 12)
    (lo := (34097 / 200000000)) (hi := (85243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000341 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000341 / 2000000) = 1/(2000000 / 2000341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2829 : Bounds (34097 / 200000000) (85243 / 500000000) (Real.log (2000341 / 2000000)) := by
  have h := reflection_log_2829_neg
  have he : Real.log (2000341 / 2000000) = -Real.log (2000000 / 2000341) := by
    rw [show ((2000341 / 2000000) : ℝ) = ((2000000 / 2000341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2830_neg : (85257 / 500000000) ≤ -Real.log (1999659 / 2000000) ∧
    -Real.log (1999659 / 2000000) ≤ (34103 / 200000000) := by
  have h := checkLog_sound (w := (341 / 3999659)) (n := 12)
    (lo := (85257 / 500000000)) (hi := (34103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999659) = 1/(1999659 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2830 : Bounds (-34103 / 200000000) (-85257 / 500000000) (Real.log (1999659 / 2000000)) := by
  have h := reflection_log_2830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2831_neg : (20525147 / 250000000) ≤ -Real.log (200000 / 217113) ∧
    -Real.log (200000 / 217113) ≤ (82100589 / 1000000000) := by
  have h := checkLog_sound (w := (17113 / 417113)) (n := 12)
    (lo := (20525147 / 250000000)) (hi := (82100589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217113 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217113 / 200000) = 1/(200000 / 217113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2831 : Bounds (20525147 / 250000000) (82100589 / 1000000000) (Real.log (217113 / 200000)) := by
  have h := reflection_log_2831_neg
  have he : Real.log (217113 / 200000) = -Real.log (200000 / 217113) := by
    rw [show ((217113 / 200000) : ℝ) = ((200000 / 217113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2832_neg : (8944889 / 100000000) ≤ -Real.log (182887 / 200000) ∧
    -Real.log (182887 / 200000) ≤ (89448891 / 1000000000) := by
  have h := checkLog_sound (w := (17113 / 382887)) (n := 12)
    (lo := (8944889 / 100000000)) (hi := (89448891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182887) = 1/(182887 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2832 : Bounds (-89448891 / 1000000000) (-8944889 / 100000000) (Real.log (182887 / 200000)) := by
  have h := reflection_log_2832_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2833_neg : (20576037 / 250000000) ≤ -Real.log (500000 / 542893) ∧
    -Real.log (500000 / 542893) ≤ (82304149 / 1000000000) := by
  have h := checkLog_sound (w := (42893 / 1042893)) (n := 12)
    (lo := (20576037 / 250000000)) (hi := (82304149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542893 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542893 / 500000) = 1/(500000 / 542893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2833 : Bounds (20576037 / 250000000) (82304149 / 1000000000) (Real.log (542893 / 500000)) := by
  have h := reflection_log_2833_neg
  have he : Real.log (542893 / 500000) = -Real.log (500000 / 542893) := by
    rw [show ((542893 / 500000) : ℝ) = ((500000 / 542893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2834_neg : (89690599 / 1000000000) ≤ -Real.log (457107 / 500000) ∧
    -Real.log (457107 / 500000) ≤ (448453 / 5000000) := by
  have h := checkLog_sound (w := (42893 / 957107)) (n := 12)
    (lo := (89690599 / 1000000000)) (hi := (448453 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457107) = 1/(457107 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2834 : Bounds (-448453 / 5000000) (-89690599 / 1000000000) (Real.log (457107 / 500000)) := by
  have h := reflection_log_2834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2835_neg : (147729 / 20000000) ≤ -Real.log (248160190551 / 250000000000) ∧
    -Real.log (248160190551 / 250000000000) ≤ (7386451 / 1000000000) := by
  have h := checkLog_sound (w := (1839809449 / 498160190551)) (n := 12)
    (lo := (147729 / 20000000)) (hi := (7386451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248160190551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248160190551) = 1/(248160190551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2835 : Bounds (-7386451 / 1000000000) (-147729 / 20000000) (Real.log (248160190551 / 250000000000)) := by
  have h := reflection_log_2835_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2836_neg : (7348301 / 1000000000) ≤ -Real.log (39707145231 / 40000000000) ∧
    -Real.log (39707145231 / 40000000000) ≤ (3674151 / 500000000) := by
  have h := checkLog_sound (w := (292854769 / 79707145231)) (n := 12)
    (lo := (7348301 / 1000000000)) (hi := (3674151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39707145231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39707145231) = 1/(39707145231 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2836 : Bounds (-3674151 / 500000000) (-7348301 / 1000000000) (Real.log (39707145231 / 40000000000)) := by
  have h := reflection_log_2836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2837_neg : (171549479 / 1000000000) ≤ -Real.log (15625000000 / 18549107509) ∧
    -Real.log (15625000000 / 18549107509) ≤ (4288737 / 25000000) := by
  have h := checkLog_sound (w := (2924107509 / 34174107509)) (n := 12)
    (lo := (171549479 / 1000000000)) (hi := (4288737 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18549107509 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18549107509 / 15625000000) = 1/(15625000000 / 18549107509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2837 : Bounds (171549479 / 1000000000) (4288737 / 25000000) (Real.log (18549107509 / 15625000000)) := by
  have h := reflection_log_2837_neg
  have he : Real.log (18549107509 / 15625000000) = -Real.log (15625000000 / 18549107509) := by
    rw [show ((18549107509 / 15625000000) : ℝ) = ((15625000000 / 18549107509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2838_neg : (171994747 / 1000000000) ≤ -Real.log (250000000000 / 296917898873) ∧
    -Real.log (250000000000 / 296917898873) ≤ (42998687 / 250000000) := by
  have h := checkLog_sound (w := (46917898873 / 546917898873)) (n := 12)
    (lo := (171994747 / 1000000000)) (hi := (42998687 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296917898873 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296917898873 / 250000000000) = 1/(250000000000 / 296917898873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2838 : Bounds (171994747 / 1000000000) (42998687 / 250000000) (Real.log (296917898873 / 250000000000)) := by
  have h := reflection_log_2838_neg
  have he : Real.log (296917898873 / 250000000000) = -Real.log (250000000000 / 296917898873) := by
    rw [show ((296917898873 / 250000000000) : ℝ) = ((250000000000 / 296917898873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2839_neg : (43019649 / 125000000) ≤ -Real.log (15625000000 / 22043756027) ∧
    -Real.log (15625000000 / 22043756027) ≤ (344157193 / 1000000000) := by
  have h := checkLog_sound (w := (6418756027 / 37668756027)) (n := 12)
    (lo := (43019649 / 125000000)) (hi := (344157193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22043756027 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22043756027 / 15625000000) = 1/(15625000000 / 22043756027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2839 : Bounds (43019649 / 125000000) (344157193 / 1000000000) (Real.log (22043756027 / 15625000000)) := by
  have h := reflection_log_2839_neg
  have he : Real.log (22043756027 / 15625000000) = -Real.log (15625000000 / 22043756027) := by
    rw [show ((22043756027 / 15625000000) : ℝ) = ((15625000000 / 22043756027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2840_neg : (344363177 / 1000000000) ≤ -Real.log (500000000000 / 705545509343) ∧
    -Real.log (500000000000 / 705545509343) ≤ (172181589 / 500000000) := by
  have h := checkLog_sound (w := (205545509343 / 1205545509343)) (n := 12)
    (lo := (344363177 / 1000000000)) (hi := (172181589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705545509343 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705545509343 / 500000000000) = 1/(500000000000 / 705545509343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2840 : Bounds (344363177 / 1000000000) (172181589 / 500000000) (Real.log (705545509343 / 500000000000)) := by
  have h := reflection_log_2840_neg
  have he : Real.log (705545509343 / 500000000000) = -Real.log (500000000000 / 705545509343) := by
    rw [show ((705545509343 / 500000000000) : ℝ) = ((500000000000 / 705545509343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2841_neg : (157516437 / 1000000000) ≤ -Real.log (5000 / 5853) ∧
    -Real.log (5000 / 5853) ≤ (78758219 / 500000000) := by
  have h := checkLog_sound (w := (853 / 10853)) (n := 12)
    (lo := (157516437 / 1000000000)) (hi := (78758219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5853 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5853 / 5000) = 1/(5000 / 5853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2841 : Bounds (157516437 / 1000000000) (78758219 / 500000000) (Real.log (5853 / 5000)) := by
  have h := reflection_log_2841_neg
  have he : Real.log (5853 / 5000) = -Real.log (5000 / 5853) := by
    rw [show ((5853 / 5000) : ℝ) = ((5000 / 5853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2842_neg : (187052731 / 1000000000) ≤ -Real.log (4147 / 5000) ∧
    -Real.log (4147 / 5000) ≤ (46763183 / 250000000) := by
  have h := checkLog_sound (w := (853 / 9147)) (n := 12)
    (lo := (187052731 / 1000000000)) (hi := (46763183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4147) = 1/(4147 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2842 : Bounds (-46763183 / 250000000) (-187052731 / 1000000000) (Real.log (4147 / 5000)) := by
  have h := reflection_log_2842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2843_neg : (34117 / 200000000) ≤ -Real.log (5000000 / 5000853) ∧
    -Real.log (5000000 / 5000853) ≤ (85293 / 500000000) := by
  have h := checkLog_sound (w := (853 / 10000853)) (n := 12)
    (lo := (34117 / 200000000)) (hi := (85293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000853 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000853 / 5000000) = 1/(5000000 / 5000853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2843 : Bounds (34117 / 200000000) (85293 / 500000000) (Real.log (5000853 / 5000000)) := by
  have h := reflection_log_2843_neg
  have he : Real.log (5000853 / 5000000) = -Real.log (5000000 / 5000853) := by
    rw [show ((5000853 / 5000000) : ℝ) = ((5000000 / 5000853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2844_neg : (85307 / 500000000) ≤ -Real.log (4999147 / 5000000) ∧
    -Real.log (4999147 / 5000000) ≤ (34123 / 200000000) := by
  have h := checkLog_sound (w := (853 / 9999147)) (n := 12)
    (lo := (85307 / 500000000)) (hi := (34123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999147) = 1/(4999147 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2844 : Bounds (-34123 / 200000000) (-85307 / 500000000) (Real.log (4999147 / 5000000)) := by
  have h := reflection_log_2844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2845_neg : (41073323 / 500000000) ≤ -Real.log (200000 / 217123) ∧
    -Real.log (200000 / 217123) ≤ (82146647 / 1000000000) := by
  have h := checkLog_sound (w := (17123 / 417123)) (n := 12)
    (lo := (41073323 / 500000000)) (hi := (82146647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217123 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217123 / 200000) = 1/(200000 / 217123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2845 : Bounds (41073323 / 500000000) (82146647 / 1000000000) (Real.log (217123 / 200000)) := by
  have h := reflection_log_2845_neg
  have he : Real.log (217123 / 200000) = -Real.log (200000 / 217123) := by
    rw [show ((217123 / 200000) : ℝ) = ((200000 / 217123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2846_neg : (8950357 / 100000000) ≤ -Real.log (182877 / 200000) ∧
    -Real.log (182877 / 200000) ≤ (89503571 / 1000000000) := by
  have h := checkLog_sound (w := (17123 / 382877)) (n := 12)
    (lo := (8950357 / 100000000)) (hi := (89503571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182877) = 1/(182877 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2846 : Bounds (-89503571 / 1000000000) (-8950357 / 100000000) (Real.log (182877 / 200000)) := by
  have h := reflection_log_2846_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2847_neg : (41175559 / 500000000) ≤ -Real.log (1000000 / 1085837) ∧
    -Real.log (1000000 / 1085837) ≤ (82351119 / 1000000000) := by
  have h := checkLog_sound (w := (85837 / 2085837)) (n := 12)
    (lo := (41175559 / 500000000)) (hi := (82351119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085837 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085837 / 1000000) = 1/(1000000 / 1085837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2847 : Bounds (41175559 / 500000000) (82351119 / 1000000000) (Real.log (1085837 / 1000000)) := by
  have h := reflection_log_2847_neg
  have he : Real.log (1085837 / 1000000) = -Real.log (1000000 / 1085837) := by
    rw [show ((1085837 / 1000000) : ℝ) = ((1000000 / 1085837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2848_neg : (44873193 / 500000000) ≤ -Real.log (914163 / 1000000) ∧
    -Real.log (914163 / 1000000) ≤ (89746387 / 1000000000) := by
  have h := checkLog_sound (w := (85837 / 1914163)) (n := 12)
    (lo := (44873193 / 500000000)) (hi := (89746387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914163) = 1/(914163 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2848 : Bounds (-89746387 / 1000000000) (-44873193 / 500000000) (Real.log (914163 / 1000000)) := by
  have h := reflection_log_2848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2849_neg : (1848817 / 250000000) ≤ -Real.log (992632009431 / 1000000000000) ∧
    -Real.log (992632009431 / 1000000000000) ≤ (7395269 / 1000000000) := by
  have h := checkLog_sound (w := (7367990569 / 1992632009431)) (n := 12)
    (lo := (1848817 / 250000000)) (hi := (7395269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992632009431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992632009431) = 1/(992632009431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2849 : Bounds (-7395269 / 1000000000) (-1848817 / 250000000) (Real.log (992632009431 / 1000000000000)) := by
  have h := reflection_log_2849_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2850_neg : (1839231 / 250000000) ≤ -Real.log (39706802871 / 40000000000) ∧
    -Real.log (39706802871 / 40000000000) ≤ (294277 / 40000000) := by
  have h := checkLog_sound (w := (293197129 / 79706802871)) (n := 12)
    (lo := (1839231 / 250000000)) (hi := (294277 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39706802871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39706802871) = 1/(39706802871 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2850 : Bounds (-294277 / 40000000) (-1839231 / 250000000) (Real.log (39706802871 / 40000000000)) := by
  have h := reflection_log_2850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2851_neg : (171650217 / 1000000000) ≤ -Real.log (250000000000 / 296815619241) ∧
    -Real.log (250000000000 / 296815619241) ≤ (85825109 / 500000000) := by
  have h := checkLog_sound (w := (46815619241 / 546815619241)) (n := 12)
    (lo := (171650217 / 1000000000)) (hi := (85825109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296815619241 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296815619241 / 250000000000) = 1/(250000000000 / 296815619241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2851 : Bounds (171650217 / 1000000000) (85825109 / 500000000) (Real.log (296815619241 / 250000000000)) := by
  have h := reflection_log_2851_neg
  have he : Real.log (296815619241 / 250000000000) = -Real.log (250000000000 / 296815619241) := by
    rw [show ((296815619241 / 250000000000) : ℝ) = ((250000000000 / 296815619241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2852_neg : (5378047 / 31250000) ≤ -Real.log (100000000000 / 118779364293) ∧
    -Real.log (100000000000 / 118779364293) ≤ (34419501 / 200000000) := by
  have h := checkLog_sound (w := (18779364293 / 218779364293)) (n := 12)
    (lo := (5378047 / 31250000)) (hi := (34419501 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118779364293 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118779364293 / 100000000000) = 1/(100000000000 / 118779364293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2852 : Bounds (5378047 / 31250000) (34419501 / 200000000) (Real.log (118779364293 / 100000000000)) := by
  have h := reflection_log_2852_neg
  have he : Real.log (118779364293 / 100000000000) = -Real.log (100000000000 / 118779364293) := by
    rw [show ((118779364293 / 100000000000) : ℝ) = ((100000000000 / 118779364293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2853_neg : (344363177 / 1000000000) ≤ -Real.log (250000000000 / 352772754671) ∧
    -Real.log (250000000000 / 352772754671) ≤ (172181589 / 500000000) := by
  have h := checkLog_sound (w := (102772754671 / 602772754671)) (n := 12)
    (lo := (344363177 / 1000000000)) (hi := (172181589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352772754671 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352772754671 / 250000000000) = 1/(250000000000 / 352772754671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2853 : Bounds (344363177 / 1000000000) (172181589 / 500000000) (Real.log (352772754671 / 250000000000)) := by
  have h := reflection_log_2853_neg
  have he : Real.log (352772754671 / 250000000000) = -Real.log (250000000000 / 352772754671) := by
    rw [show ((352772754671 / 250000000000) : ℝ) = ((250000000000 / 352772754671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2854_neg : (344569169 / 1000000000) ≤ -Real.log (7812500000 / 11026419701) ∧
    -Real.log (7812500000 / 11026419701) ≤ (34456917 / 100000000) := by
  have h := checkLog_sound (w := (3213919701 / 18838919701)) (n := 12)
    (lo := (344569169 / 1000000000)) (hi := (34456917 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11026419701 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11026419701 / 7812500000) = 1/(7812500000 / 11026419701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2854 : Bounds (344569169 / 1000000000) (34456917 / 100000000) (Real.log (11026419701 / 7812500000)) := by
  have h := reflection_log_2854_neg
  have he : Real.log (11026419701 / 7812500000) = -Real.log (7812500000 / 11026419701) := by
    rw [show ((11026419701 / 7812500000) : ℝ) = ((7812500000 / 11026419701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2855_neg : (7880093 / 50000000) ≤ -Real.log (10000 / 11707) ∧
    -Real.log (10000 / 11707) ≤ (157601861 / 1000000000) := by
  have h := checkLog_sound (w := (1707 / 21707)) (n := 12)
    (lo := (7880093 / 50000000)) (hi := (157601861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11707 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11707 / 10000) = 1/(10000 / 11707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2855 : Bounds (7880093 / 50000000) (157601861 / 1000000000) (Real.log (11707 / 10000)) := by
  have h := reflection_log_2855_neg
  have he : Real.log (11707 / 10000) = -Real.log (10000 / 11707) := by
    rw [show ((11707 / 10000) : ℝ) = ((10000 / 11707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2856_neg : (187173307 / 1000000000) ≤ -Real.log (8293 / 10000) ∧
    -Real.log (8293 / 10000) ≤ (46793327 / 250000000) := by
  have h := checkLog_sound (w := (1707 / 18293)) (n := 12)
    (lo := (187173307 / 1000000000)) (hi := (46793327 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8293) = 1/(8293 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2856 : Bounds (-46793327 / 250000000) (-187173307 / 1000000000) (Real.log (8293 / 10000)) := by
  have h := reflection_log_2856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2857_neg : (34137 / 200000000) ≤ -Real.log (10000000 / 10001707) ∧
    -Real.log (10000000 / 10001707) ≤ (85343 / 500000000) := by
  have h := checkLog_sound (w := (1707 / 20001707)) (n := 12)
    (lo := (34137 / 200000000)) (hi := (85343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001707 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001707 / 10000000) = 1/(10000000 / 10001707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2857 : Bounds (34137 / 200000000) (85343 / 500000000) (Real.log (10001707 / 10000000)) := by
  have h := reflection_log_2857_neg
  have he : Real.log (10001707 / 10000000) = -Real.log (10000000 / 10001707) := by
    rw [show ((10001707 / 10000000) : ℝ) = ((10000000 / 10001707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2858_neg : (85357 / 500000000) ≤ -Real.log (9998293 / 10000000) ∧
    -Real.log (9998293 / 10000000) ≤ (34143 / 200000000) := by
  have h := checkLog_sound (w := (1707 / 19998293)) (n := 12)
    (lo := (85357 / 500000000)) (hi := (34143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998293) = 1/(9998293 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2858 : Bounds (-34143 / 200000000) (-85357 / 500000000) (Real.log (9998293 / 10000000)) := by
  have h := reflection_log_2858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2859_neg : (82193623 / 1000000000) ≤ -Real.log (500000 / 542833) ∧
    -Real.log (500000 / 542833) ≤ (10274203 / 125000000) := by
  have h := checkLog_sound (w := (42833 / 1042833)) (n := 12)
    (lo := (82193623 / 1000000000)) (hi := (10274203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542833 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542833 / 500000) = 1/(500000 / 542833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2859 : Bounds (82193623 / 1000000000) (10274203 / 125000000) (Real.log (542833 / 500000)) := by
  have h := reflection_log_2859_neg
  have he : Real.log (542833 / 500000) = -Real.log (500000 / 542833) := by
    rw [show ((542833 / 500000) : ℝ) = ((500000 / 542833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2860_neg : (89559347 / 1000000000) ≤ -Real.log (457167 / 500000) ∧
    -Real.log (457167 / 500000) ≤ (22389837 / 250000000) := by
  have h := checkLog_sound (w := (42833 / 957167)) (n := 12)
    (lo := (89559347 / 1000000000)) (hi := (22389837 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457167) = 1/(457167 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2860 : Bounds (-22389837 / 250000000) (-89559347 / 1000000000) (Real.log (457167 / 500000)) := by
  have h := reflection_log_2860_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2861_neg : (16479617 / 200000000) ≤ -Real.log (15625 / 16967) ∧
    -Real.log (15625 / 16967) ≤ (41199043 / 500000000) := by
  have h := checkLog_sound (w := (671 / 16296)) (n := 12)
    (lo := (16479617 / 200000000)) (hi := (41199043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16967 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16967 / 15625) = 1/(15625 / 16967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2861 : Bounds (16479617 / 200000000) (41199043 / 500000000) (Real.log (16967 / 15625)) := by
  have h := reflection_log_2861_neg
  have he : Real.log (16967 / 15625) = -Real.log (15625 / 16967) := by
    rw [show ((16967 / 15625) : ℝ) = ((15625 / 16967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2862_neg : (1403159 / 15625000) ≤ -Real.log (14283 / 15625) ∧
    -Real.log (14283 / 15625) ≤ (89802177 / 1000000000) := by
  have h := checkLog_sound (w := (671 / 14954)) (n := 12)
    (lo := (1403159 / 15625000)) (hi := (89802177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14283) = 1/(14283 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2862 : Bounds (-89802177 / 1000000000) (-1403159 / 15625000) (Real.log (14283 / 15625)) := by
  have h := reflection_log_2862_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2863_neg : (7404091 / 1000000000) ≤ -Real.log (242339661 / 244140625) ∧
    -Real.log (242339661 / 244140625) ≤ (1851023 / 250000000) := by
  have h := checkLog_sound (w := (900482 / 243240143)) (n := 12)
    (lo := (7404091 / 1000000000)) (hi := (1851023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242339661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242339661) = 1/(242339661 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2863 : Bounds (-1851023 / 250000000) (-7404091 / 1000000000) (Real.log (242339661 / 244140625)) := by
  have h := reflection_log_2863_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2864_neg : (1841431 / 250000000) ≤ -Real.log (248165334111 / 250000000000) ∧
    -Real.log (248165334111 / 250000000000) ≤ (294629 / 40000000) := by
  have h := checkLog_sound (w := (1834665889 / 498165334111)) (n := 12)
    (lo := (1841431 / 250000000)) (hi := (294629 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248165334111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248165334111) = 1/(248165334111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2864 : Bounds (-294629 / 40000000) (-1841431 / 250000000) (Real.log (248165334111 / 250000000000)) := by
  have h := reflection_log_2864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2865_neg : (171752971 / 1000000000) ≤ -Real.log (250000000000 / 296846119689) ∧
    -Real.log (250000000000 / 296846119689) ≤ (42938243 / 250000000) := by
  have h := checkLog_sound (w := (46846119689 / 546846119689)) (n := 12)
    (lo := (171752971 / 1000000000)) (hi := (42938243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296846119689 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296846119689 / 250000000000) = 1/(250000000000 / 296846119689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2865 : Bounds (171752971 / 1000000000) (42938243 / 250000000) (Real.log (296846119689 / 250000000000)) := by
  have h := reflection_log_2865_neg
  have he : Real.log (296846119689 / 250000000000) = -Real.log (250000000000 / 296846119689) := by
    rw [show ((296846119689 / 250000000000) : ℝ) = ((250000000000 / 296846119689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2866_neg : (86100131 / 500000000) ≤ -Real.log (62500000000 / 74244731499) ∧
    -Real.log (62500000000 / 74244731499) ≤ (172200263 / 1000000000) := by
  have h := checkLog_sound (w := (11744731499 / 136744731499)) (n := 12)
    (lo := (86100131 / 500000000)) (hi := (172200263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74244731499 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74244731499 / 62500000000) = 1/(62500000000 / 74244731499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2866 : Bounds (86100131 / 500000000) (172200263 / 1000000000) (Real.log (74244731499 / 62500000000)) := by
  have h := reflection_log_2866_neg
  have he : Real.log (74244731499 / 62500000000) = -Real.log (62500000000 / 74244731499) := by
    rw [show ((74244731499 / 62500000000) : ℝ) = ((62500000000 / 74244731499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2867_neg : (344569169 / 1000000000) ≤ -Real.log (500000000000 / 705690860863) ∧
    -Real.log (500000000000 / 705690860863) ≤ (34456917 / 100000000) := by
  have h := checkLog_sound (w := (205690860863 / 1205690860863)) (n := 12)
    (lo := (344569169 / 1000000000)) (hi := (34456917 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705690860863 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705690860863 / 500000000000) = 1/(500000000000 / 705690860863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2867 : Bounds (344569169 / 1000000000) (34456917 / 100000000) (Real.log (705690860863 / 500000000000)) := by
  have h := reflection_log_2867_neg
  have he : Real.log (705690860863 / 500000000000) = -Real.log (500000000000 / 705690860863) := by
    rw [show ((705690860863 / 500000000000) : ℝ) = ((500000000000 / 705690860863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2868_neg : (673389 / 1953125) ≤ -Real.log (250000000000 / 352918123719) ∧
    -Real.log (250000000000 / 352918123719) ≤ (344775169 / 1000000000) := by
  have h := checkLog_sound (w := (102918123719 / 602918123719)) (n := 12)
    (lo := (673389 / 1953125)) (hi := (344775169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352918123719 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352918123719 / 250000000000) = 1/(250000000000 / 352918123719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2868 : Bounds (673389 / 1953125) (344775169 / 1000000000) (Real.log (352918123719 / 250000000000)) := by
  have h := reflection_log_2868_neg
  have he : Real.log (352918123719 / 250000000000) = -Real.log (250000000000 / 352918123719) := by
    rw [show ((352918123719 / 250000000000) : ℝ) = ((250000000000 / 352918123719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2869_neg : (6307491 / 40000000) ≤ -Real.log (2500 / 2927) ∧
    -Real.log (2500 / 2927) ≤ (39421819 / 250000000) := by
  have h := checkLog_sound (w := (427 / 5427)) (n := 12)
    (lo := (6307491 / 40000000)) (hi := (39421819 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2927 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2927 / 2500) = 1/(2500 / 2927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2869 : Bounds (6307491 / 40000000) (39421819 / 250000000) (Real.log (2927 / 2500)) := by
  have h := reflection_log_2869_neg
  have he : Real.log (2927 / 2500) = -Real.log (2500 / 2927) := by
    rw [show ((2927 / 2500) : ℝ) = ((2500 / 2927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2870_neg : (93646949 / 500000000) ≤ -Real.log (2073 / 2500) ∧
    -Real.log (2073 / 2500) ≤ (187293899 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 4573)) (n := 12)
    (lo := (93646949 / 500000000)) (hi := (187293899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2073) = 1/(2073 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2870 : Bounds (-187293899 / 1000000000) (-93646949 / 500000000) (Real.log (2073 / 2500)) := by
  have h := reflection_log_2870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2871_neg : (34157 / 200000000) ≤ -Real.log (2500000 / 2500427) ∧
    -Real.log (2500000 / 2500427) ≤ (85393 / 500000000) := by
  have h := checkLog_sound (w := (427 / 5000427)) (n := 12)
    (lo := (34157 / 200000000)) (hi := (85393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500427 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500427 / 2500000) = 1/(2500000 / 2500427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2871 : Bounds (34157 / 200000000) (85393 / 500000000) (Real.log (2500427 / 2500000)) := by
  have h := reflection_log_2871_neg
  have he : Real.log (2500427 / 2500000) = -Real.log (2500000 / 2500427) := by
    rw [show ((2500427 / 2500000) : ℝ) = ((2500000 / 2500427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2872_neg : (85407 / 500000000) ≤ -Real.log (2499573 / 2500000) ∧
    -Real.log (2499573 / 2500000) ≤ (34163 / 200000000) := by
  have h := checkLog_sound (w := (427 / 4999573)) (n := 12)
    (lo := (85407 / 500000000)) (hi := (34163 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499573) = 1/(2499573 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2872 : Bounds (-34163 / 200000000) (-85407 / 500000000) (Real.log (2499573 / 2500000)) := by
  have h := reflection_log_2872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2873_neg : (41120299 / 500000000) ≤ -Real.log (1000000 / 1085717) ∧
    -Real.log (1000000 / 1085717) ≤ (82240599 / 1000000000) := by
  have h := checkLog_sound (w := (85717 / 2085717)) (n := 12)
    (lo := (41120299 / 500000000)) (hi := (82240599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085717 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085717 / 1000000) = 1/(1000000 / 1085717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2873 : Bounds (41120299 / 500000000) (82240599 / 1000000000) (Real.log (1085717 / 1000000)) := by
  have h := reflection_log_2873_neg
  have he : Real.log (1085717 / 1000000) = -Real.log (1000000 / 1085717) := by
    rw [show ((1085717 / 1000000) : ℝ) = ((1000000 / 1085717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2874_neg : (89615127 / 1000000000) ≤ -Real.log (914283 / 1000000) ∧
    -Real.log (914283 / 1000000) ≤ (11201891 / 125000000) := by
  have h := checkLog_sound (w := (85717 / 1914283)) (n := 12)
    (lo := (89615127 / 1000000000)) (hi := (11201891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914283) = 1/(914283 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2874 : Bounds (-11201891 / 125000000) (-89615127 / 1000000000) (Real.log (914283 / 1000000)) := by
  have h := reflection_log_2874_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2875_neg : (1648901 / 20000000) ≤ -Real.log (1000000 / 1085939) ∧
    -Real.log (1000000 / 1085939) ≤ (82445051 / 1000000000) := by
  have h := checkLog_sound (w := (85939 / 2085939)) (n := 12)
    (lo := (1648901 / 20000000)) (hi := (82445051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085939 / 1000000) = 1/(1000000 / 1085939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2875 : Bounds (1648901 / 20000000) (82445051 / 1000000000) (Real.log (1085939 / 1000000)) := by
  have h := reflection_log_2875_neg
  have he : Real.log (1085939 / 1000000) = -Real.log (1000000 / 1085939) := by
    rw [show ((1085939 / 1000000) : ℝ) = ((1000000 / 1085939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2876_neg : (8985797 / 100000000) ≤ -Real.log (914061 / 1000000) ∧
    -Real.log (914061 / 1000000) ≤ (89857971 / 1000000000) := by
  have h := checkLog_sound (w := (85939 / 1914061)) (n := 12)
    (lo := (8985797 / 100000000)) (hi := (89857971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 914061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 914061) = 1/(914061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2876 : Bounds (-89857971 / 1000000000) (-8985797 / 100000000) (Real.log (914061 / 1000000)) := by
  have h := reflection_log_2876_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2877_neg : (7412919 / 1000000000) ≤ -Real.log (992614488279 / 1000000000000) ∧
    -Real.log (992614488279 / 1000000000000) ≤ (185323 / 25000000) := by
  have h := checkLog_sound (w := (7385511721 / 1992614488279)) (n := 12)
    (lo := (7412919 / 1000000000)) (hi := (185323 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992614488279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992614488279) = 1/(992614488279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2877 : Bounds (-185323 / 25000000) (-7412919 / 1000000000) (Real.log (992614488279 / 1000000000000)) := by
  have h := reflection_log_2877_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2878_neg : (7374529 / 1000000000) ≤ -Real.log (992652595911 / 1000000000000) ∧
    -Real.log (992652595911 / 1000000000000) ≤ (737453 / 100000000) := by
  have h := checkLog_sound (w := (7347404089 / 1992652595911)) (n := 12)
    (lo := (7374529 / 1000000000)) (hi := (737453 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992652595911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992652595911) = 1/(992652595911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2878 : Bounds (-737453 / 100000000) (-7374529 / 1000000000) (Real.log (992652595911 / 1000000000000)) := by
  have h := reflection_log_2878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2879_neg : (6874229 / 40000000) ≤ -Real.log (500000000000 / 593753247079) ∧
    -Real.log (500000000000 / 593753247079) ≤ (85927863 / 500000000) := by
  have h := checkLog_sound (w := (93753247079 / 1093753247079)) (n := 12)
    (lo := (6874229 / 40000000)) (hi := (85927863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593753247079 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593753247079 / 500000000000) = 1/(500000000000 / 593753247079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2879 : Bounds (6874229 / 40000000) (85927863 / 500000000) (Real.log (593753247079 / 500000000000)) := by
  have h := reflection_log_2879_neg
  have he : Real.log (593753247079 / 500000000000) = -Real.log (500000000000 / 593753247079) := by
    rw [show ((593753247079 / 500000000000) : ℝ) = ((500000000000 / 593753247079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
