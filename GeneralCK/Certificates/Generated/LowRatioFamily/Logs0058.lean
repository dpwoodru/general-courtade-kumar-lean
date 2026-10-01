import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3712_neg : (35363 / 200000000) ≤ -Real.log (1249779 / 1250000) ∧
    -Real.log (1249779 / 1250000) ≤ (11051 / 62500000) := by
  have h := checkLog_sound (w := (221 / 2499779)) (n := 12)
    (lo := (35363 / 200000000)) (hi := (11051 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249779) = 1/(1249779 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3712 : Bounds (-11051 / 62500000) (-35363 / 200000000) (Real.log (1249779 / 1250000)) := by
  have h := reflection_log_3712_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3713_neg : (85043107 / 1000000000) ≤ -Real.log (250000 / 272191) ∧
    -Real.log (250000 / 272191) ≤ (21260777 / 250000000) := by
  have h := checkLog_sound (w := (22191 / 522191)) (n := 12)
    (lo := (85043107 / 1000000000)) (hi := (21260777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272191 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272191 / 250000) = 1/(250000 / 272191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3713 : Bounds (85043107 / 1000000000) (21260777 / 250000000) (Real.log (272191 / 250000)) := by
  have h := reflection_log_3713_neg
  have he : Real.log (272191 / 250000) = -Real.log (250000 / 272191) := by
    rw [show ((272191 / 250000) : ℝ) = ((250000 / 272191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3714_neg : (92953359 / 1000000000) ≤ -Real.log (227809 / 250000) ∧
    -Real.log (227809 / 250000) ≤ (1161917 / 12500000) := by
  have h := checkLog_sound (w := (22191 / 477809)) (n := 12)
    (lo := (92953359 / 1000000000)) (hi := (1161917 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227809) = 1/(227809 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3714 : Bounds (-1161917 / 12500000) (-92953359 / 1000000000) (Real.log (227809 / 250000)) := by
  have h := reflection_log_3714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3715_neg : (85251579 / 1000000000) ≤ -Real.log (1000000 / 1088991) ∧
    -Real.log (1000000 / 1088991) ≤ (4262579 / 50000000) := by
  have h := checkLog_sound (w := (88991 / 2088991)) (n := 12)
    (lo := (85251579 / 1000000000)) (hi := (4262579 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088991 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088991 / 1000000) = 1/(1000000 / 1088991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3715 : Bounds (85251579 / 1000000000) (4262579 / 50000000) (Real.log (1088991 / 1000000)) := by
  have h := reflection_log_3715_neg
  have he : Real.log (1088991 / 1000000) = -Real.log (1000000 / 1088991) := by
    rw [show ((1088991 / 1000000) : ℝ) = ((1000000 / 1088991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3716_neg : (46601251 / 500000000) ≤ -Real.log (911009 / 1000000) ∧
    -Real.log (911009 / 1000000) ≤ (93202503 / 1000000000) := by
  have h := checkLog_sound (w := (88991 / 1911009)) (n := 12)
    (lo := (46601251 / 500000000)) (hi := (93202503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911009) = 1/(911009 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3716 : Bounds (-93202503 / 1000000000) (-46601251 / 500000000) (Real.log (911009 / 1000000)) := by
  have h := reflection_log_3716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3717_neg : (7950923 / 1000000000) ≤ -Real.log (992080601919 / 1000000000000) ∧
    -Real.log (992080601919 / 1000000000000) ≤ (1987731 / 250000000) := by
  have h := checkLog_sound (w := (7919398081 / 1992080601919)) (n := 12)
    (lo := (7950923 / 1000000000)) (hi := (1987731 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992080601919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992080601919) = 1/(992080601919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3717 : Bounds (-1987731 / 250000000) (-7950923 / 1000000000) (Real.log (992080601919 / 1000000000000)) := by
  have h := reflection_log_3717_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3718_neg : (7910251 / 1000000000) ≤ -Real.log (62007559519 / 62500000000) ∧
    -Real.log (62007559519 / 62500000000) ≤ (1977563 / 250000000) := by
  have h := checkLog_sound (w := (492440481 / 124507559519)) (n := 12)
    (lo := (7910251 / 1000000000)) (hi := (1977563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62007559519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62007559519) = 1/(62007559519 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3718 : Bounds (-1977563 / 250000000) (-7910251 / 1000000000) (Real.log (62007559519 / 62500000000)) := by
  have h := reflection_log_3718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3719_neg : (177996467 / 1000000000) ≤ -Real.log (250000000000 / 298705275033) ∧
    -Real.log (250000000000 / 298705275033) ≤ (44499117 / 250000000) := by
  have h := checkLog_sound (w := (48705275033 / 548705275033)) (n := 12)
    (lo := (177996467 / 1000000000)) (hi := (44499117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298705275033 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298705275033 / 250000000000) = 1/(250000000000 / 298705275033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3719 : Bounds (177996467 / 1000000000) (44499117 / 250000000) (Real.log (298705275033 / 250000000000)) := by
  have h := reflection_log_3719_neg
  have he : Real.log (298705275033 / 250000000000) = -Real.log (250000000000 / 298705275033) := by
    rw [show ((298705275033 / 250000000000) : ℝ) = ((250000000000 / 298705275033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3720_neg : (178454081 / 1000000000) ≤ -Real.log (62500000000 / 74710499567) ∧
    -Real.log (62500000000 / 74710499567) ≤ (89227041 / 500000000) := by
  have h := checkLog_sound (w := (12210499567 / 137210499567)) (n := 12)
    (lo := (178454081 / 1000000000)) (hi := (89227041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74710499567 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74710499567 / 62500000000) = 1/(62500000000 / 74710499567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3720 : Bounds (178454081 / 1000000000) (89227041 / 500000000) (Real.log (74710499567 / 62500000000)) := by
  have h := reflection_log_3720_neg
  have he : Real.log (74710499567 / 62500000000) = -Real.log (62500000000 / 74710499567) := by
    rw [show ((74710499567 / 62500000000) : ℝ) = ((62500000000 / 74710499567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3721_neg : (71429707 / 200000000) ≤ -Real.log (500000000000 / 714624073849) ∧
    -Real.log (500000000000 / 714624073849) ≤ (44643567 / 125000000) := by
  have h := checkLog_sound (w := (214624073849 / 1214624073849)) (n := 12)
    (lo := (71429707 / 200000000)) (hi := (44643567 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714624073849 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714624073849 / 500000000000) = 1/(500000000000 / 714624073849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3721 : Bounds (71429707 / 200000000) (44643567 / 125000000) (Real.log (714624073849 / 500000000000)) := by
  have h := reflection_log_3721_neg
  have he : Real.log (714624073849 / 500000000000) = -Real.log (500000000000 / 714624073849) := by
    rw [show ((714624073849 / 500000000000) : ℝ) = ((500000000000 / 714624073849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3722_neg : (44669373 / 125000000) ≤ -Real.log (100000000000 / 142954324587) ∧
    -Real.log (100000000000 / 142954324587) ≤ (71470997 / 200000000) := by
  have h := checkLog_sound (w := (42954324587 / 242954324587)) (n := 12)
    (lo := (44669373 / 125000000)) (hi := (71470997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142954324587 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142954324587 / 100000000000) = 1/(100000000000 / 142954324587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3722 : Bounds (44669373 / 125000000) (71470997 / 200000000) (Real.log (142954324587 / 100000000000)) := by
  have h := reflection_log_3722_neg
  have he : Real.log (142954324587 / 100000000000) = -Real.log (100000000000 / 142954324587) := by
    rw [show ((142954324587 / 100000000000) : ℝ) = ((100000000000 / 142954324587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3723_neg : (81441931 / 500000000) ≤ -Real.log (10000 / 11769) ∧
    -Real.log (10000 / 11769) ≤ (162883863 / 1000000000) := by
  have h := checkLog_sound (w := (1769 / 21769)) (n := 12)
    (lo := (81441931 / 500000000)) (hi := (162883863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11769 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11769 / 10000) = 1/(10000 / 11769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3723 : Bounds (81441931 / 500000000) (162883863 / 1000000000) (Real.log (11769 / 10000)) := by
  have h := reflection_log_3723_neg
  have he : Real.log (11769 / 10000) = -Real.log (10000 / 11769) := by
    rw [show ((11769 / 10000) : ℝ) = ((10000 / 11769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3724_neg : (194677579 / 1000000000) ≤ -Real.log (8231 / 10000) ∧
    -Real.log (8231 / 10000) ≤ (9733879 / 50000000) := by
  have h := checkLog_sound (w := (1769 / 18231)) (n := 12)
    (lo := (194677579 / 1000000000)) (hi := (9733879 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8231) = 1/(8231 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3724 : Bounds (-9733879 / 50000000) (-194677579 / 1000000000) (Real.log (8231 / 10000)) := by
  have h := reflection_log_3724_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3725_neg : (44221 / 250000000) ≤ -Real.log (10000000 / 10001769) ∧
    -Real.log (10000000 / 10001769) ≤ (35377 / 200000000) := by
  have h := checkLog_sound (w := (1769 / 20001769)) (n := 12)
    (lo := (44221 / 250000000)) (hi := (35377 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001769 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001769 / 10000000) = 1/(10000000 / 10001769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3725 : Bounds (44221 / 250000000) (35377 / 200000000) (Real.log (10001769 / 10000000)) := by
  have h := reflection_log_3725_neg
  have he : Real.log (10001769 / 10000000) = -Real.log (10000000 / 10001769) := by
    rw [show ((10001769 / 10000000) : ℝ) = ((10000000 / 10001769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3726_neg : (35383 / 200000000) ≤ -Real.log (9998231 / 10000000) ∧
    -Real.log (9998231 / 10000000) ≤ (44229 / 250000000) := by
  have h := checkLog_sound (w := (1769 / 19998231)) (n := 12)
    (lo := (35383 / 200000000)) (hi := (44229 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998231) = 1/(9998231 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3726 : Bounds (-44229 / 250000000) (-35383 / 200000000) (Real.log (9998231 / 10000000)) := by
  have h := reflection_log_3726_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3727_neg : (21272487 / 250000000) ≤ -Real.log (200000 / 217763) ∧
    -Real.log (200000 / 217763) ≤ (85089949 / 1000000000) := by
  have h := checkLog_sound (w := (17763 / 417763)) (n := 12)
    (lo := (21272487 / 250000000)) (hi := (85089949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217763 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217763 / 200000) = 1/(200000 / 217763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3727 : Bounds (21272487 / 250000000) (85089949 / 1000000000) (Real.log (217763 / 200000)) := by
  have h := reflection_log_3727_neg
  have he : Real.log (217763 / 200000) = -Real.log (200000 / 217763) := by
    rw [show ((217763 / 200000) : ℝ) = ((200000 / 217763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3728_neg : (5813083 / 62500000) ≤ -Real.log (182237 / 200000) ∧
    -Real.log (182237 / 200000) ≤ (93009329 / 1000000000) := by
  have h := checkLog_sound (w := (17763 / 382237)) (n := 12)
    (lo := (5813083 / 62500000)) (hi := (93009329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182237) = 1/(182237 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3728 : Bounds (-93009329 / 1000000000) (-5813083 / 62500000) (Real.log (182237 / 200000)) := by
  have h := reflection_log_3728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3729_neg : (8529841 / 100000000) ≤ -Real.log (500000 / 544521) ∧
    -Real.log (500000 / 544521) ≤ (85298411 / 1000000000) := by
  have h := checkLog_sound (w := (44521 / 1044521)) (n := 12)
    (lo := (8529841 / 100000000)) (hi := (85298411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544521 / 500000) = 1/(500000 / 544521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3729 : Bounds (8529841 / 100000000) (85298411 / 1000000000) (Real.log (544521 / 500000)) := by
  have h := reflection_log_3729_neg
  have he : Real.log (544521 / 500000) = -Real.log (500000 / 544521) := by
    rw [show ((544521 / 500000) : ℝ) = ((500000 / 544521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3730_neg : (18651697 / 200000000) ≤ -Real.log (455479 / 500000) ∧
    -Real.log (455479 / 500000) ≤ (46629243 / 500000000) := by
  have h := checkLog_sound (w := (44521 / 955479)) (n := 12)
    (lo := (18651697 / 200000000)) (hi := (46629243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455479) = 1/(455479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3730 : Bounds (-46629243 / 500000000) (-18651697 / 200000000) (Real.log (455479 / 500000)) := by
  have h := reflection_log_3730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3731_neg : (318403 / 40000000) ≤ -Real.log (248017880559 / 250000000000) ∧
    -Real.log (248017880559 / 250000000000) ≤ (1990019 / 250000000) := by
  have h := checkLog_sound (w := (1982119441 / 498017880559)) (n := 12)
    (lo := (318403 / 40000000)) (hi := (1990019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248017880559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248017880559) = 1/(248017880559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3731 : Bounds (-1990019 / 250000000) (-318403 / 40000000) (Real.log (248017880559 / 250000000000)) := by
  have h := reflection_log_3731_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3732_neg : (7919379 / 1000000000) ≤ -Real.log (39684475831 / 40000000000) ∧
    -Real.log (39684475831 / 40000000000) ≤ (395969 / 50000000) := by
  have h := checkLog_sound (w := (315524169 / 79684475831)) (n := 12)
    (lo := (7919379 / 1000000000)) (hi := (395969 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39684475831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39684475831) = 1/(39684475831 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3732 : Bounds (-395969 / 50000000) (-7919379 / 1000000000) (Real.log (39684475831 / 40000000000)) := by
  have h := reflection_log_3732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3733_neg : (178099277 / 1000000000) ≤ -Real.log (500000000000 / 597471973309) ∧
    -Real.log (500000000000 / 597471973309) ≤ (89049639 / 500000000) := by
  have h := checkLog_sound (w := (97471973309 / 1097471973309)) (n := 12)
    (lo := (178099277 / 1000000000)) (hi := (89049639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597471973309 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597471973309 / 500000000000) = 1/(500000000000 / 597471973309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3733 : Bounds (178099277 / 1000000000) (89049639 / 500000000) (Real.log (597471973309 / 500000000000)) := by
  have h := reflection_log_3733_neg
  have he : Real.log (597471973309 / 500000000000) = -Real.log (500000000000 / 597471973309) := by
    rw [show ((597471973309 / 500000000000) : ℝ) = ((500000000000 / 597471973309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3734_neg : (5579903 / 31250000) ≤ -Real.log (250000000000 / 298872725197) ∧
    -Real.log (250000000000 / 298872725197) ≤ (178556897 / 1000000000) := by
  have h := checkLog_sound (w := (48872725197 / 548872725197)) (n := 12)
    (lo := (5579903 / 31250000)) (hi := (178556897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298872725197 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298872725197 / 250000000000) = 1/(250000000000 / 298872725197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3734 : Bounds (5579903 / 31250000) (178556897 / 1000000000) (Real.log (298872725197 / 250000000000)) := by
  have h := reflection_log_3734_neg
  have he : Real.log (298872725197 / 250000000000) = -Real.log (250000000000 / 298872725197) := by
    rw [show ((298872725197 / 250000000000) : ℝ) = ((250000000000 / 298872725197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3735_neg : (44669373 / 125000000) ≤ -Real.log (250000000000 / 357385811467) ∧
    -Real.log (250000000000 / 357385811467) ≤ (71470997 / 200000000) := by
  have h := checkLog_sound (w := (107385811467 / 607385811467)) (n := 12)
    (lo := (44669373 / 125000000)) (hi := (71470997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357385811467 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357385811467 / 250000000000) = 1/(250000000000 / 357385811467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3735 : Bounds (44669373 / 125000000) (71470997 / 200000000) (Real.log (357385811467 / 250000000000)) := by
  have h := reflection_log_3735_neg
  have he : Real.log (357385811467 / 250000000000) = -Real.log (250000000000 / 357385811467) := by
    rw [show ((357385811467 / 250000000000) : ℝ) = ((250000000000 / 357385811467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3736_neg : (357561441 / 1000000000) ≤ -Real.log (500000000000 / 714919207873) ∧
    -Real.log (500000000000 / 714919207873) ≤ (178780721 / 500000000) := by
  have h := checkLog_sound (w := (214919207873 / 1214919207873)) (n := 12)
    (lo := (357561441 / 1000000000)) (hi := (178780721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714919207873 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714919207873 / 500000000000) = 1/(500000000000 / 714919207873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3736 : Bounds (357561441 / 1000000000) (178780721 / 500000000) (Real.log (714919207873 / 500000000000)) := by
  have h := reflection_log_3736_neg
  have he : Real.log (714919207873 / 500000000000) = -Real.log (500000000000 / 714919207873) := by
    rw [show ((714919207873 / 500000000000) : ℝ) = ((500000000000 / 714919207873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3737_neg : (40742207 / 250000000) ≤ -Real.log (1000 / 1177) ∧
    -Real.log (1000 / 1177) ≤ (162968829 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 2177)) (n := 12)
    (lo := (40742207 / 250000000)) (hi := (162968829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1177 / 1000) = 1/(1000 / 1177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3737 : Bounds (40742207 / 250000000) (162968829 / 1000000000) (Real.log (1177 / 1000)) := by
  have h := reflection_log_3737_neg
  have he : Real.log (1177 / 1000) = -Real.log (1000 / 1177) := by
    rw [show ((1177 / 1000) : ℝ) = ((1000 / 1177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3738_neg : (97399539 / 500000000) ≤ -Real.log (823 / 1000) ∧
    -Real.log (823 / 1000) ≤ (194799079 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 1823)) (n := 12)
    (lo := (97399539 / 500000000)) (hi := (194799079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 823) = 1/(823 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3738 : Bounds (-194799079 / 1000000000) (-97399539 / 500000000) (Real.log (823 / 1000)) := by
  have h := reflection_log_3738_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3739_neg : (22123 / 125000000) ≤ -Real.log (1000000 / 1000177) ∧
    -Real.log (1000000 / 1000177) ≤ (35397 / 200000000) := by
  have h := checkLog_sound (w := (177 / 2000177)) (n := 12)
    (lo := (22123 / 125000000)) (hi := (35397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000177 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000177 / 1000000) = 1/(1000000 / 1000177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3739 : Bounds (22123 / 125000000) (35397 / 200000000) (Real.log (1000177 / 1000000)) := by
  have h := reflection_log_3739_neg
  have he : Real.log (1000177 / 1000000) = -Real.log (1000000 / 1000177) := by
    rw [show ((1000177 / 1000000) : ℝ) = ((1000000 / 1000177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3740_neg : (35403 / 200000000) ≤ -Real.log (999823 / 1000000) ∧
    -Real.log (999823 / 1000000) ≤ (22127 / 125000000) := by
  have h := checkLog_sound (w := (177 / 1999823)) (n := 12)
    (lo := (35403 / 200000000)) (hi := (22127 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999823) = 1/(999823 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3740 : Bounds (-22127 / 125000000) (-35403 / 200000000) (Real.log (999823 / 1000000)) := by
  have h := reflection_log_3740_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3741_neg : (85135869 / 1000000000) ≤ -Real.log (200000 / 217773) ∧
    -Real.log (200000 / 217773) ≤ (8513587 / 100000000) := by
  have h := checkLog_sound (w := (17773 / 417773)) (n := 12)
    (lo := (85135869 / 1000000000)) (hi := (8513587 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217773 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217773 / 200000) = 1/(200000 / 217773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3741 : Bounds (85135869 / 1000000000) (8513587 / 100000000) (Real.log (217773 / 200000)) := by
  have h := reflection_log_3741_neg
  have he : Real.log (217773 / 200000) = -Real.log (200000 / 217773) := by
    rw [show ((217773 / 200000) : ℝ) = ((200000 / 217773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3742_neg : (93064203 / 1000000000) ≤ -Real.log (182227 / 200000) ∧
    -Real.log (182227 / 200000) ≤ (23266051 / 250000000) := by
  have h := checkLog_sound (w := (17773 / 382227)) (n := 12)
    (lo := (93064203 / 1000000000)) (hi := (23266051 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182227) = 1/(182227 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3742 : Bounds (-23266051 / 250000000) (-93064203 / 1000000000) (Real.log (182227 / 200000)) := by
  have h := reflection_log_3742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3743_neg : (85345239 / 1000000000) ≤ -Real.log (1000000 / 1089093) ∧
    -Real.log (1000000 / 1089093) ≤ (2133631 / 25000000) := by
  have h := checkLog_sound (w := (89093 / 2089093)) (n := 12)
    (lo := (85345239 / 1000000000)) (hi := (2133631 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089093 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089093 / 1000000) = 1/(1000000 / 1089093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3743 : Bounds (85345239 / 1000000000) (2133631 / 25000000) (Real.log (1089093 / 1000000)) := by
  have h := reflection_log_3743_neg
  have he : Real.log (1089093 / 1000000) = -Real.log (1000000 / 1089093) := by
    rw [show ((1089093 / 1000000) : ℝ) = ((1000000 / 1089093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3744_neg : (11664309 / 125000000) ≤ -Real.log (910907 / 1000000) ∧
    -Real.log (910907 / 1000000) ≤ (93314473 / 1000000000) := by
  have h := checkLog_sound (w := (89093 / 1910907)) (n := 12)
    (lo := (11664309 / 125000000)) (hi := (93314473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910907) = 1/(910907 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3744 : Bounds (-93314473 / 1000000000) (-11664309 / 125000000) (Real.log (910907 / 1000000)) := by
  have h := reflection_log_3744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3745_neg : (498077 / 62500000) ≤ -Real.log (992062437351 / 1000000000000) ∧
    -Real.log (992062437351 / 1000000000000) ≤ (7969233 / 1000000000) := by
  have h := checkLog_sound (w := (7937562649 / 1992062437351)) (n := 12)
    (lo := (498077 / 62500000)) (hi := (7969233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992062437351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992062437351) = 1/(992062437351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3745 : Bounds (-7969233 / 1000000000) (-498077 / 62500000) (Real.log (992062437351 / 1000000000000)) := by
  have h := reflection_log_3745_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3746_neg : (3964167 / 500000000) ≤ -Real.log (39684120471 / 40000000000) ∧
    -Real.log (39684120471 / 40000000000) ≤ (1585667 / 200000000) := by
  have h := checkLog_sound (w := (315879529 / 79684120471)) (n := 12)
    (lo := (3964167 / 500000000)) (hi := (1585667 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39684120471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39684120471) = 1/(39684120471 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3746 : Bounds (-1585667 / 200000000) (-3964167 / 500000000) (Real.log (39684120471 / 40000000000)) := by
  have h := reflection_log_3746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3747_neg : (178200073 / 1000000000) ≤ -Real.log (10000000000 / 11950643977) ∧
    -Real.log (10000000000 / 11950643977) ≤ (89100037 / 500000000) := by
  have h := checkLog_sound (w := (1950643977 / 21950643977)) (n := 12)
    (lo := (178200073 / 1000000000)) (hi := (89100037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11950643977 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11950643977 / 10000000000) = 1/(10000000000 / 11950643977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3747 : Bounds (178200073 / 1000000000) (89100037 / 500000000) (Real.log (11950643977 / 10000000000)) := by
  have h := reflection_log_3747_neg
  have he : Real.log (11950643977 / 10000000000) = -Real.log (10000000000 / 11950643977) := by
    rw [show ((11950643977 / 10000000000) : ℝ) = ((10000000000 / 11950643977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3748_neg : (1395779 / 7812500) ≤ -Real.log (250000000000 / 298903455567) ∧
    -Real.log (250000000000 / 298903455567) ≤ (178659713 / 1000000000) := by
  have h := checkLog_sound (w := (48903455567 / 548903455567)) (n := 12)
    (lo := (1395779 / 7812500)) (hi := (178659713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298903455567 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298903455567 / 250000000000) = 1/(250000000000 / 298903455567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3748 : Bounds (1395779 / 7812500) (178659713 / 1000000000) (Real.log (298903455567 / 250000000000)) := by
  have h := reflection_log_3748_neg
  have he : Real.log (298903455567 / 250000000000) = -Real.log (250000000000 / 298903455567) := by
    rw [show ((298903455567 / 250000000000) : ℝ) = ((250000000000 / 298903455567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3749_neg : (357561441 / 1000000000) ≤ -Real.log (7812500000 / 11170612623) ∧
    -Real.log (7812500000 / 11170612623) ≤ (178780721 / 500000000) := by
  have h := checkLog_sound (w := (3358112623 / 18983112623)) (n := 12)
    (lo := (357561441 / 1000000000)) (hi := (178780721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11170612623 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11170612623 / 7812500000) = 1/(7812500000 / 11170612623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3749 : Bounds (357561441 / 1000000000) (178780721 / 500000000) (Real.log (11170612623 / 7812500000)) := by
  have h := reflection_log_3749_neg
  have he : Real.log (11170612623 / 7812500000) = -Real.log (7812500000 / 11170612623) := by
    rw [show ((11170612623 / 7812500000) : ℝ) = ((7812500000 / 11170612623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3750_neg : (178883953 / 500000000) ≤ -Real.log (125000000000 / 178766707169) ∧
    -Real.log (125000000000 / 178766707169) ≤ (357767907 / 1000000000) := by
  have h := checkLog_sound (w := (53766707169 / 303766707169)) (n := 12)
    (lo := (178883953 / 500000000)) (hi := (357767907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178766707169 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178766707169 / 125000000000) = 1/(125000000000 / 178766707169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3750 : Bounds (178883953 / 500000000) (357767907 / 1000000000) (Real.log (178766707169 / 125000000000)) := by
  have h := reflection_log_3750_neg
  have he : Real.log (178766707169 / 125000000000) = -Real.log (125000000000 / 178766707169) := by
    rw [show ((178766707169 / 125000000000) : ℝ) = ((125000000000 / 178766707169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3751_neg : (81526893 / 500000000) ≤ -Real.log (10000 / 11771) ∧
    -Real.log (10000 / 11771) ≤ (163053787 / 1000000000) := by
  have h := checkLog_sound (w := (1771 / 21771)) (n := 12)
    (lo := (81526893 / 500000000)) (hi := (163053787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11771 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11771 / 10000) = 1/(10000 / 11771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3751 : Bounds (81526893 / 500000000) (163053787 / 1000000000) (Real.log (11771 / 10000)) := by
  have h := reflection_log_3751_neg
  have he : Real.log (11771 / 10000) = -Real.log (10000 / 11771) := by
    rw [show ((11771 / 10000) : ℝ) = ((10000 / 11771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3752_neg : (12182537 / 62500000) ≤ -Real.log (8229 / 10000) ∧
    -Real.log (8229 / 10000) ≤ (194920593 / 1000000000) := by
  have h := checkLog_sound (w := (1771 / 18229)) (n := 12)
    (lo := (12182537 / 62500000)) (hi := (194920593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8229) = 1/(8229 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3752 : Bounds (-194920593 / 1000000000) (-12182537 / 62500000) (Real.log (8229 / 10000)) := by
  have h := reflection_log_3752_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3753_neg : (44271 / 250000000) ≤ -Real.log (10000000 / 10001771) ∧
    -Real.log (10000000 / 10001771) ≤ (35417 / 200000000) := by
  have h := checkLog_sound (w := (1771 / 20001771)) (n := 12)
    (lo := (44271 / 250000000)) (hi := (35417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001771 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001771 / 10000000) = 1/(10000000 / 10001771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3753 : Bounds (44271 / 250000000) (35417 / 200000000) (Real.log (10001771 / 10000000)) := by
  have h := reflection_log_3753_neg
  have he : Real.log (10001771 / 10000000) = -Real.log (10000000 / 10001771) := by
    rw [show ((10001771 / 10000000) : ℝ) = ((10000000 / 10001771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3754_neg : (35423 / 200000000) ≤ -Real.log (9998229 / 10000000) ∧
    -Real.log (9998229 / 10000000) ≤ (44279 / 250000000) := by
  have h := checkLog_sound (w := (1771 / 19998229)) (n := 12)
    (lo := (35423 / 200000000)) (hi := (44279 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998229) = 1/(9998229 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3754 : Bounds (-44279 / 250000000) (-35423 / 200000000) (Real.log (9998229 / 10000000)) := by
  have h := reflection_log_3754_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3755_neg : (17036541 / 200000000) ≤ -Real.log (250000 / 272229) ∧
    -Real.log (250000 / 272229) ≤ (42591353 / 500000000) := by
  have h := checkLog_sound (w := (22229 / 522229)) (n := 12)
    (lo := (17036541 / 200000000)) (hi := (42591353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272229 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272229 / 250000) = 1/(250000 / 272229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3755 : Bounds (17036541 / 200000000) (42591353 / 500000000) (Real.log (272229 / 250000)) := by
  have h := reflection_log_3755_neg
  have he : Real.log (272229 / 250000) = -Real.log (250000 / 272229) := by
    rw [show ((272229 / 250000) : ℝ) = ((250000 / 272229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3756_neg : (93120179 / 1000000000) ≤ -Real.log (227771 / 250000) ∧
    -Real.log (227771 / 250000) ≤ (4656009 / 50000000) := by
  have h := checkLog_sound (w := (22229 / 477771)) (n := 12)
    (lo := (93120179 / 1000000000)) (hi := (4656009 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227771) = 1/(227771 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3756 : Bounds (-4656009 / 50000000) (-93120179 / 1000000000) (Real.log (227771 / 250000)) := by
  have h := reflection_log_3756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3757_neg : (42696033 / 500000000) ≤ -Real.log (125000 / 136143) ∧
    -Real.log (125000 / 136143) ≤ (85392067 / 1000000000) := by
  have h := checkLog_sound (w := (11143 / 261143)) (n := 12)
    (lo := (42696033 / 500000000)) (hi := (85392067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136143 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136143 / 125000) = 1/(125000 / 136143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3757 : Bounds (42696033 / 500000000) (85392067 / 1000000000) (Real.log (136143 / 125000)) := by
  have h := reflection_log_3757_neg
  have he : Real.log (136143 / 125000) = -Real.log (125000 / 136143) := by
    rw [show ((136143 / 125000) : ℝ) = ((125000 / 136143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3758_neg : (46685231 / 500000000) ≤ -Real.log (113857 / 125000) ∧
    -Real.log (113857 / 125000) ≤ (93370463 / 1000000000) := by
  have h := checkLog_sound (w := (11143 / 238857)) (n := 12)
    (lo := (46685231 / 500000000)) (hi := (93370463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113857) = 1/(113857 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3758 : Bounds (-93370463 / 1000000000) (-46685231 / 500000000) (Real.log (113857 / 125000)) := by
  have h := reflection_log_3758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3759_neg : (1595679 / 200000000) ≤ -Real.log (15500833551 / 15625000000) ∧
    -Real.log (15500833551 / 15625000000) ≤ (1994599 / 250000000) := by
  have h := checkLog_sound (w := (124166449 / 31125833551)) (n := 12)
    (lo := (1595679 / 200000000)) (hi := (1994599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15500833551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15500833551) = 1/(15500833551 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3759 : Bounds (-1994599 / 250000000) (-1595679 / 200000000) (Real.log (15500833551 / 15625000000)) := by
  have h := reflection_log_3759_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3760_neg : (7937473 / 1000000000) ≤ -Real.log (62005871559 / 62500000000) ∧
    -Real.log (62005871559 / 62500000000) ≤ (3968737 / 500000000) := by
  have h := checkLog_sound (w := (494128441 / 124505871559)) (n := 12)
    (lo := (7937473 / 1000000000)) (hi := (3968737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62005871559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62005871559) = 1/(62005871559 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3760 : Bounds (-3968737 / 500000000) (-7937473 / 1000000000) (Real.log (62005871559 / 62500000000)) := by
  have h := reflection_log_3760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3761_neg : (35660577 / 200000000) ≤ -Real.log (500000000000 / 597593635713) ∧
    -Real.log (500000000000 / 597593635713) ≤ (89151443 / 500000000) := by
  have h := checkLog_sound (w := (97593635713 / 1097593635713)) (n := 12)
    (lo := (35660577 / 200000000)) (hi := (89151443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597593635713 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597593635713 / 500000000000) = 1/(500000000000 / 597593635713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3761 : Bounds (35660577 / 200000000) (89151443 / 500000000) (Real.log (597593635713 / 500000000000)) := by
  have h := reflection_log_3761_neg
  have he : Real.log (597593635713 / 500000000000) = -Real.log (500000000000 / 597593635713) := by
    rw [show ((597593635713 / 500000000000) : ℝ) = ((500000000000 / 597593635713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3762_neg : (5586329 / 31250000) ≤ -Real.log (125000000000 / 149467094689) ∧
    -Real.log (125000000000 / 149467094689) ≤ (178762529 / 1000000000) := by
  have h := checkLog_sound (w := (24467094689 / 274467094689)) (n := 12)
    (lo := (5586329 / 31250000)) (hi := (178762529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149467094689 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149467094689 / 125000000000) = 1/(125000000000 / 149467094689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3762 : Bounds (5586329 / 31250000) (178762529 / 1000000000) (Real.log (149467094689 / 125000000000)) := by
  have h := reflection_log_3762_neg
  have he : Real.log (149467094689 / 125000000000) = -Real.log (125000000000 / 149467094689) := by
    rw [show ((149467094689 / 125000000000) : ℝ) = ((125000000000 / 149467094689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3763_neg : (178883953 / 500000000) ≤ -Real.log (20000000000 / 28602673147) ∧
    -Real.log (20000000000 / 28602673147) ≤ (357767907 / 1000000000) := by
  have h := checkLog_sound (w := (8602673147 / 48602673147)) (n := 12)
    (lo := (178883953 / 500000000)) (hi := (357767907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28602673147 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28602673147 / 20000000000) = 1/(20000000000 / 28602673147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3763 : Bounds (178883953 / 500000000) (357767907 / 1000000000) (Real.log (28602673147 / 20000000000)) := by
  have h := reflection_log_3763_neg
  have he : Real.log (28602673147 / 20000000000) = -Real.log (20000000000 / 28602673147) := by
    rw [show ((28602673147 / 20000000000) : ℝ) = ((20000000000 / 28602673147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3764_neg : (178987189 / 500000000) ≤ -Real.log (500000000000 / 715214485357) ∧
    -Real.log (500000000000 / 715214485357) ≤ (357974379 / 1000000000) := by
  have h := checkLog_sound (w := (215214485357 / 1215214485357)) (n := 12)
    (lo := (178987189 / 500000000)) (hi := (357974379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715214485357 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715214485357 / 500000000000) = 1/(500000000000 / 715214485357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3764 : Bounds (178987189 / 500000000) (357974379 / 1000000000) (Real.log (715214485357 / 500000000000)) := by
  have h := reflection_log_3764_neg
  have he : Real.log (715214485357 / 500000000000) = -Real.log (500000000000 / 715214485357) := by
    rw [show ((715214485357 / 500000000000) : ℝ) = ((500000000000 / 715214485357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3765_neg : (163138737 / 1000000000) ≤ -Real.log (2500 / 2943) ∧
    -Real.log (2500 / 2943) ≤ (81569369 / 500000000) := by
  have h := checkLog_sound (w := (443 / 5443)) (n := 12)
    (lo := (163138737 / 1000000000)) (hi := (81569369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2943 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2943 / 2500) = 1/(2500 / 2943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3765 : Bounds (163138737 / 1000000000) (81569369 / 500000000) (Real.log (2943 / 2500)) := by
  have h := reflection_log_3765_neg
  have he : Real.log (2943 / 2500) = -Real.log (2500 / 2943) := by
    rw [show ((2943 / 2500) : ℝ) = ((2500 / 2943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3766_neg : (195042121 / 1000000000) ≤ -Real.log (2057 / 2500) ∧
    -Real.log (2057 / 2500) ≤ (97521061 / 500000000) := by
  have h := checkLog_sound (w := (443 / 4557)) (n := 12)
    (lo := (195042121 / 1000000000)) (hi := (97521061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2057) = 1/(2057 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3766 : Bounds (-97521061 / 500000000) (-195042121 / 1000000000) (Real.log (2057 / 2500)) := by
  have h := reflection_log_3766_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3767_neg : (5537 / 31250000) ≤ -Real.log (2500000 / 2500443) ∧
    -Real.log (2500000 / 2500443) ≤ (35437 / 200000000) := by
  have h := checkLog_sound (w := (443 / 5000443)) (n := 12)
    (lo := (5537 / 31250000)) (hi := (35437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500443 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500443 / 2500000) = 1/(2500000 / 2500443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3767 : Bounds (5537 / 31250000) (35437 / 200000000) (Real.log (2500443 / 2500000)) := by
  have h := reflection_log_3767_neg
  have he : Real.log (2500443 / 2500000) = -Real.log (2500000 / 2500443) := by
    rw [show ((2500443 / 2500000) : ℝ) = ((2500000 / 2500443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3768_neg : (35443 / 200000000) ≤ -Real.log (2499557 / 2500000) ∧
    -Real.log (2499557 / 2500000) ≤ (2769 / 15625000) := by
  have h := checkLog_sound (w := (443 / 4999557)) (n := 12)
    (lo := (35443 / 200000000)) (hi := (2769 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499557) = 1/(2499557 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3768 : Bounds (-2769 / 15625000) (-35443 / 200000000) (Real.log (2499557 / 2500000)) := by
  have h := reflection_log_3768_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3769_neg : (4261477 / 50000000) ≤ -Real.log (1000000 / 1088967) ∧
    -Real.log (1000000 / 1088967) ≤ (85229541 / 1000000000) := by
  have h := checkLog_sound (w := (88967 / 2088967)) (n := 12)
    (lo := (4261477 / 50000000)) (hi := (85229541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088967 / 1000000) = 1/(1000000 / 1088967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3769 : Bounds (4261477 / 50000000) (85229541 / 1000000000) (Real.log (1088967 / 1000000)) := by
  have h := reflection_log_3769_neg
  have he : Real.log (1088967 / 1000000) = -Real.log (1000000 / 1088967) := by
    rw [show ((1088967 / 1000000) : ℝ) = ((1000000 / 1088967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3770_neg : (46588079 / 500000000) ≤ -Real.log (911033 / 1000000) ∧
    -Real.log (911033 / 1000000) ≤ (93176159 / 1000000000) := by
  have h := checkLog_sound (w := (88967 / 1911033)) (n := 12)
    (lo := (46588079 / 500000000)) (hi := (93176159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911033) = 1/(911033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3770 : Bounds (-93176159 / 1000000000) (-46588079 / 500000000) (Real.log (911033 / 1000000)) := by
  have h := reflection_log_3770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3771_neg : (85438891 / 1000000000) ≤ -Real.log (200000 / 217839) ∧
    -Real.log (200000 / 217839) ≤ (21359723 / 250000000) := by
  have h := checkLog_sound (w := (17839 / 417839)) (n := 12)
    (lo := (85438891 / 1000000000)) (hi := (21359723 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217839 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217839 / 200000) = 1/(200000 / 217839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3771 : Bounds (85438891 / 1000000000) (21359723 / 250000000) (Real.log (217839 / 200000)) := by
  have h := reflection_log_3771_neg
  have he : Real.log (217839 / 200000) = -Real.log (200000 / 217839) := by
    rw [show ((217839 / 200000) : ℝ) = ((200000 / 217839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3772_neg : (18685291 / 200000000) ≤ -Real.log (182161 / 200000) ∧
    -Real.log (182161 / 200000) ≤ (11678307 / 125000000) := by
  have h := checkLog_sound (w := (17839 / 382161)) (n := 12)
    (lo := (18685291 / 200000000)) (hi := (11678307 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182161) = 1/(182161 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3772 : Bounds (-11678307 / 125000000) (-18685291 / 200000000) (Real.log (182161 / 200000)) := by
  have h := reflection_log_3772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3773_neg : (7987563 / 1000000000) ≤ -Real.log (39681770079 / 40000000000) ∧
    -Real.log (39681770079 / 40000000000) ≤ (1996891 / 250000000) := by
  have h := checkLog_sound (w := (318229921 / 79681770079)) (n := 12)
    (lo := (7987563 / 1000000000)) (hi := (1996891 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39681770079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39681770079) = 1/(39681770079 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3773 : Bounds (-1996891 / 250000000) (-7987563 / 1000000000) (Real.log (39681770079 / 40000000000)) := by
  have h := reflection_log_3773_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3774_neg : (7946617 / 1000000000) ≤ -Real.log (992084872911 / 1000000000000) ∧
    -Real.log (992084872911 / 1000000000000) ≤ (3973309 / 500000000) := by
  have h := checkLog_sound (w := (7915127089 / 1992084872911)) (n := 12)
    (lo := (7946617 / 1000000000)) (hi := (3973309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992084872911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992084872911) = 1/(992084872911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3774 : Bounds (-3973309 / 500000000) (-7946617 / 1000000000) (Real.log (992084872911 / 1000000000000)) := by
  have h := reflection_log_3774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3775_neg : (89202849 / 500000000) ≤ -Real.log (500000000000 / 597655079453) ∧
    -Real.log (500000000000 / 597655079453) ≤ (178405699 / 1000000000) := by
  have h := checkLog_sound (w := (97655079453 / 1097655079453)) (n := 12)
    (lo := (89202849 / 500000000)) (hi := (178405699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597655079453 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597655079453 / 500000000000) = 1/(500000000000 / 597655079453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3775 : Bounds (89202849 / 500000000) (178405699 / 1000000000) (Real.log (597655079453 / 500000000000)) := by
  have h := reflection_log_3775_neg
  have he : Real.log (597655079453 / 500000000000) = -Real.log (500000000000 / 597655079453) := by
    rw [show ((597655079453 / 500000000000) : ℝ) = ((500000000000 / 597655079453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
