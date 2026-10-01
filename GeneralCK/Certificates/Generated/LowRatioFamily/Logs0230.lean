import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14720_neg : (18747861 / 40000000) ≤ -Real.log (100000 / 159791) ∧
    -Real.log (100000 / 159791) ≤ (234348263 / 500000000) := by
  have h := checkLog_sound (w := (59791 / 259791)) (n := 12)
    (lo := (18747861 / 40000000)) (hi := (234348263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159791 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159791 / 100000) = 1/(100000 / 159791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14720 : Bounds (18747861 / 40000000) (234348263 / 500000000) (Real.log (159791 / 100000)) := by
  have h := reflection_log_14720_neg
  have he : Real.log (159791 / 100000) = -Real.log (100000 / 159791) := by
    rw [show ((159791 / 100000) : ℝ) = ((100000 / 159791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14721_neg : (455539667 / 500000000) ≤ -Real.log (40209 / 100000) ∧
    -Real.log (40209 / 100000) ≤ (113884917 / 125000000) := by
  have h := checkLog_sound (w := (9791 / 90209)) (n := 12)
    (lo := (108966077 / 500000000)) (hi := (43586431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40209) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 40209) = 1/(40209 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14721 : Bounds (-113884917 / 125000000) (-455539667 / 500000000) (Real.log (40209 / 100000)) := by
  have h := reflection_log_14721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14722_neg : (469807359 / 1000000000) ≤ -Real.log (500000 / 799843) ∧
    -Real.log (500000 / 799843) ≤ (367037 / 781250) := by
  have h := checkLog_sound (w := (299843 / 1299843)) (n := 12)
    (lo := (469807359 / 1000000000)) (hi := (367037 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((799843 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(799843 / 500000) = 1/(500000 / 799843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14722 : Bounds (469807359 / 1000000000) (367037 / 781250) (Real.log (799843 / 500000)) := by
  have h := reflection_log_14722_neg
  have he : Real.log (799843 / 500000) = -Real.log (500000 / 799843) := by
    rw [show ((799843 / 500000) : ℝ) = ((500000 / 799843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14723_neg : (915506039 / 1000000000) ≤ -Real.log (200157 / 500000) ∧
    -Real.log (200157 / 500000) ≤ (915506041 / 1000000000) := by
  have h := checkLog_sound (w := (49843 / 450157)) (n := 12)
    (lo := (222358859 / 1000000000)) (hi := (11117943 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 200157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 200157) = 1/(200157 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14723 : Bounds (-915506041 / 1000000000) (-915506039 / 1000000000) (Real.log (200157 / 500000)) := by
  have h := reflection_log_14723_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14724_neg : (445698679 / 1000000000) ≤ -Real.log (160094175351 / 250000000000) ∧
    -Real.log (160094175351 / 250000000000) ≤ (11142467 / 25000000) := by
  have h := checkLog_sound (w := (89905824649 / 410094175351)) (n := 12)
    (lo := (445698679 / 1000000000)) (hi := (11142467 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 160094175351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 160094175351) = 1/(160094175351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14724 : Bounds (-11142467 / 25000000) (-445698679 / 1000000000) (Real.log (160094175351 / 250000000000)) := by
  have h := reflection_log_14724_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14725_neg : (442382809 / 1000000000) ≤ -Real.log (6425036319 / 10000000000) ∧
    -Real.log (6425036319 / 10000000000) ≤ (44238281 / 100000000) := by
  have h := checkLog_sound (w := (3574963681 / 16425036319)) (n := 12)
    (lo := (442382809 / 1000000000)) (hi := (44238281 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 6425036319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 6425036319) = 1/(6425036319 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14725 : Bounds (-44238281 / 100000000) (-442382809 / 1000000000) (Real.log (6425036319 / 10000000000)) := by
  have h := reflection_log_14725_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14726_neg : (1379775859 / 1000000000) ≤ -Real.log (500000000000 / 1987005396801) ∧
    -Real.log (500000000000 / 1987005396801) ≤ (1379775861 / 1000000000) := by
  have h := checkLog_sound (w := (987005396801 / 2987005396801)) (n := 12)
    (lo := (686628679 / 1000000000)) (hi := (17165717 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1987005396801 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1987005396801 / 1000000000000) = 1/(500000000000 / 1987005396801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14726 : Bounds (1379775859 / 1000000000) (1379775861 / 1000000000) (Real.log (1987005396801 / 500000000000)) := by
  have h := reflection_log_14726_neg
  have he : Real.log (1987005396801 / 500000000000) = -Real.log (500000000000 / 1987005396801) := by
    rw [show ((1987005396801 / 500000000000) : ℝ) = ((500000000000 / 1987005396801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14727_neg : (1385313399 / 1000000000) ≤ -Real.log (100000000000 / 399607807871) ∧
    -Real.log (100000000000 / 399607807871) ≤ (1385313401 / 1000000000) := by
  have h := checkLog_sound (w := (199607807871 / 599607807871)) (n := 12)
    (lo := (692166219 / 1000000000)) (hi := (34608311 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399607807871 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(399607807871 / 200000000000) = 1/(100000000000 / 399607807871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14727 : Bounds (1385313399 / 1000000000) (1385313401 / 1000000000) (Real.log (399607807871 / 100000000000)) := by
  have h := reflection_log_14727_neg
  have he : Real.log (399607807871 / 100000000000) = -Real.log (100000000000 / 399607807871) := by
    rw [show ((399607807871 / 100000000000) : ℝ) = ((100000000000 / 399607807871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14728_neg : (3771482979 / 1000000000) ≤ -Real.log (250000000000 / 10861111111111) ∧
    -Real.log (250000000000 / 10861111111111) ≤ (754296597 / 200000000) := by
  have h := checkLog_sound (w := (2861111111111 / 18861111111111)) (n := 12)
    (lo := (305747079 / 1000000000)) (hi := (7643677 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10861111111111 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10861111111111 / 8000000000000) = 1/(250000000000 / 10861111111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14728 : Bounds (3771482979 / 1000000000) (754296597 / 200000000) (Real.log (10861111111111 / 250000000000)) := by
  have h := reflection_log_14728_neg
  have he : Real.log (10861111111111 / 250000000000) = -Real.log (250000000000 / 10861111111111) := by
    rw [show ((10861111111111 / 250000000000) : ℝ) = ((250000000000 / 10861111111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14729_neg : (3794467213 / 1000000000) ≤ -Real.log (500000000000 / 22227272727273) ∧
    -Real.log (500000000000 / 22227272727273) ≤ (3794467219 / 1000000000) := by
  have h := checkLog_sound (w := (6227272727273 / 38227272727273)) (n := 12)
    (lo := (328731313 / 1000000000)) (hi := (164365657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22227272727273 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(22227272727273 / 16000000000000) = 1/(500000000000 / 22227272727273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14729 : Bounds (3794467213 / 1000000000) (3794467219 / 1000000000) (Real.log (22227272727273 / 500000000000)) := by
  have h := reflection_log_14729_neg
  have he : Real.log (22227272727273 / 500000000000) = -Real.log (500000000000 / 22227272727273) := by
    rw [show ((22227272727273 / 500000000000) : ℝ) = ((500000000000 / 22227272727273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14730_neg : (41963293 / 62500000) ≤ -Real.log (1000 / 1957) ∧
    -Real.log (1000 / 1957) ≤ (671412689 / 1000000000) := by
  have h := checkLog_sound (w := (957 / 2957)) (n := 12)
    (lo := (41963293 / 62500000)) (hi := (671412689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1957 / 1000) = 1/(1000 / 1957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14730 : Bounds (41963293 / 62500000) (671412689 / 1000000000) (Real.log (1957 / 1000)) := by
  have h := reflection_log_14730_neg
  have he : Real.log (1957 / 1000) = -Real.log (1000 / 1957) := by
    rw [show ((1957 / 1000) : ℝ) = ((1000 / 1957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14731_neg : (3146555161 / 1000000000) ≤ -Real.log (43 / 1000) ∧
    -Real.log (43 / 1000) ≤ (1573277583 / 500000000) := by
  have h := checkLog_sound (w := (39 / 211)) (n := 12)
    (lo := (373966441 / 1000000000)) (hi := (186983221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 86) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 86) = 1/(43 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14731 : Bounds (-1573277583 / 500000000) (-3146555161 / 1000000000) (Real.log (43 / 1000)) := by
  have h := reflection_log_14731_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14732_neg : (478271 / 500000000) ≤ -Real.log (1000000 / 1000957) ∧
    -Real.log (1000000 / 1000957) ≤ (956543 / 1000000000) := by
  have h := checkLog_sound (w := (957 / 2000957)) (n := 12)
    (lo := (478271 / 500000000)) (hi := (956543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000957 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000957 / 1000000) = 1/(1000000 / 1000957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14732 : Bounds (478271 / 500000000) (956543 / 1000000000) (Real.log (1000957 / 1000000)) := by
  have h := reflection_log_14732_neg
  have he : Real.log (1000957 / 1000000) = -Real.log (1000000 / 1000957) := by
    rw [show ((1000957 / 1000000) : ℝ) = ((1000000 / 1000957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14733_neg : (478729 / 500000000) ≤ -Real.log (999043 / 1000000) ∧
    -Real.log (999043 / 1000000) ≤ (957459 / 1000000000) := by
  have h := checkLog_sound (w := (957 / 1999043)) (n := 12)
    (lo := (478729 / 500000000)) (hi := (957459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999043) = 1/(999043 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14733 : Bounds (-957459 / 1000000000) (-478729 / 500000000) (Real.log (999043 / 1000000)) := by
  have h := reflection_log_14733_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14734_neg : (93879439 / 200000000) ≤ -Real.log (100000 / 159903) ∧
    -Real.log (100000 / 159903) ≤ (117349299 / 250000000) := by
  have h := checkLog_sound (w := (59903 / 259903)) (n := 12)
    (lo := (93879439 / 200000000)) (hi := (117349299 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159903 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159903 / 100000) = 1/(100000 / 159903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14734 : Bounds (93879439 / 200000000) (117349299 / 250000000) (Real.log (159903 / 100000)) := by
  have h := reflection_log_14734_neg
  have he : Real.log (159903 / 100000) = -Real.log (100000 / 159903) := by
    rw [show ((159903 / 100000) : ℝ) = ((100000 / 159903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14735_neg : (456934333 / 500000000) ≤ -Real.log (40097 / 100000) ∧
    -Real.log (40097 / 100000) ≤ (228467167 / 250000000) := by
  have h := checkLog_sound (w := (9903 / 90097)) (n := 12)
    (lo := (110360743 / 500000000)) (hi := (220721487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40097) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 40097) = 1/(40097 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14735 : Bounds (-228467167 / 250000000) (-456934333 / 500000000) (Real.log (40097 / 100000)) := by
  have h := reflection_log_14735_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14736_neg : (470509751 / 1000000000) ≤ -Real.log (100000 / 160081) ∧
    -Real.log (100000 / 160081) ≤ (58813719 / 125000000) := by
  have h := checkLog_sound (w := (60081 / 260081)) (n := 12)
    (lo := (470509751 / 1000000000)) (hi := (58813719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160081 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160081 / 100000) = 1/(100000 / 160081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14736 : Bounds (470509751 / 1000000000) (58813719 / 125000000) (Real.log (160081 / 100000)) := by
  have h := reflection_log_14736_neg
  have he : Real.log (160081 / 100000) = -Real.log (100000 / 160081) := by
    rw [show ((160081 / 100000) : ℝ) = ((100000 / 160081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14737_neg : (114789723 / 125000000) ≤ -Real.log (39919 / 100000) ∧
    -Real.log (39919 / 100000) ≤ (459158893 / 500000000) := by
  have h := checkLog_sound (w := (10081 / 89919)) (n := 12)
    (lo := (56292651 / 250000000)) (hi := (45034121 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39919) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 39919) = 1/(39919 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14737 : Bounds (-459158893 / 500000000) (-114789723 / 125000000) (Real.log (39919 / 100000)) := by
  have h := reflection_log_14737_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14738_neg : (447808033 / 1000000000) ≤ -Real.log (6390273439 / 10000000000) ∧
    -Real.log (6390273439 / 10000000000) ≤ (223904017 / 500000000) := by
  have h := checkLog_sound (w := (3609726561 / 16390273439)) (n := 12)
    (lo := (447808033 / 1000000000)) (hi := (223904017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 6390273439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 6390273439) = 1/(6390273439 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14738 : Bounds (-223904017 / 500000000) (-447808033 / 1000000000) (Real.log (6390273439 / 10000000000)) := by
  have h := reflection_log_14738_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14739_neg : (27779467 / 62500000) ≤ -Real.log (6411630591 / 10000000000) ∧
    -Real.log (6411630591 / 10000000000) ≤ (444471473 / 1000000000) := by
  have h := checkLog_sound (w := (3588369409 / 16411630591)) (n := 12)
    (lo := (27779467 / 62500000)) (hi := (444471473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 6411630591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 6411630591) = 1/(6411630591 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14739 : Bounds (-444471473 / 1000000000) (-27779467 / 62500000) (Real.log (6411630591 / 10000000000)) := by
  have h := reflection_log_14739_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14740_neg : (691632931 / 500000000) ≤ -Real.log (500000000000 / 1993952165997) ∧
    -Real.log (500000000000 / 1993952165997) ≤ (172908233 / 125000000) := by
  have h := checkLog_sound (w := (993952165997 / 2993952165997)) (n := 12)
    (lo := (345059341 / 500000000)) (hi := (690118683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1993952165997 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1993952165997 / 1000000000000) = 1/(500000000000 / 1993952165997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14740 : Bounds (691632931 / 500000000) (172908233 / 125000000) (Real.log (1993952165997 / 500000000000)) := by
  have h := reflection_log_14740_neg
  have he : Real.log (1993952165997 / 500000000000) = -Real.log (500000000000 / 1993952165997) := by
    rw [show ((1993952165997 / 500000000000) : ℝ) = ((500000000000 / 1993952165997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14741_neg : (694413767 / 500000000) ≤ -Real.log (100000000000 / 401014554473) ∧
    -Real.log (100000000000 / 401014554473) ≤ (1388827537 / 1000000000) := by
  have h := checkLog_sound (w := (1014554473 / 801014554473)) (n := 12)
    (lo := (1266587 / 500000000)) (hi := (101327 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401014554473 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(401014554473 / 400000000000) = 1/(100000000000 / 401014554473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14741 : Bounds (694413767 / 500000000) (1388827537 / 1000000000) (Real.log (401014554473 / 100000000000)) := by
  have h := reflection_log_14741_neg
  have he : Real.log (401014554473 / 100000000000) = -Real.log (100000000000 / 401014554473) := by
    rw [show ((401014554473 / 100000000000) : ℝ) = ((100000000000 / 401014554473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14742_neg : (3794467213 / 1000000000) ≤ -Real.log (62500000000 / 2778409090909) ∧
    -Real.log (62500000000 / 2778409090909) ≤ (3794467219 / 1000000000) := by
  have h := checkLog_sound (w := (778409090909 / 4778409090909)) (n := 12)
    (lo := (328731313 / 1000000000)) (hi := (164365657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2778409090909 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2778409090909 / 2000000000000) = 1/(62500000000 / 2778409090909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14742 : Bounds (3794467213 / 1000000000) (3794467219 / 1000000000) (Real.log (2778409090909 / 62500000000)) := by
  have h := reflection_log_14742_neg
  have he : Real.log (2778409090909 / 62500000000) = -Real.log (62500000000 / 2778409090909) := by
    rw [show ((2778409090909 / 62500000000) : ℝ) = ((62500000000 / 2778409090909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14743_neg : (477245981 / 125000000) ≤ -Real.log (500000000000 / 22755813953489) ∧
    -Real.log (500000000000 / 22755813953489) ≤ (1908983927 / 500000000) := by
  have h := checkLog_sound (w := (6755813953489 / 38755813953489)) (n := 12)
    (lo := (88057987 / 250000000)) (hi := (352231949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22755813953489 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(22755813953489 / 16000000000000) = 1/(500000000000 / 22755813953489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14743 : Bounds (477245981 / 125000000) (1908983927 / 500000000) (Real.log (22755813953489 / 500000000000)) := by
  have h := reflection_log_14743_neg
  have he : Real.log (22755813953489 / 500000000000) = -Real.log (500000000000 / 22755813953489) := by
    rw [show ((22755813953489 / 500000000000) : ℝ) = ((500000000000 / 22755813953489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14744_neg : (83990443 / 125000000) ≤ -Real.log (500 / 979) ∧
    -Real.log (500 / 979) ≤ (134384709 / 200000000) := by
  have h := checkLog_sound (w := (479 / 1479)) (n := 12)
    (lo := (83990443 / 125000000)) (hi := (134384709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((979 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(979 / 500) = 1/(500 / 979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14744 : Bounds (83990443 / 125000000) (134384709 / 200000000) (Real.log (979 / 500)) := by
  have h := reflection_log_14744_neg
  have he : Real.log (979 / 500) = -Real.log (500 / 979) := by
    rw [show ((979 / 500) : ℝ) = ((500 / 979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14745_neg : (1585042829 / 500000000) ≤ -Real.log (21 / 500) ∧
    -Real.log (21 / 500) ≤ (3170085663 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 209)) (n := 12)
    (lo := (198748469 / 500000000)) (hi := (397496939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 84) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 84) = 1/(21 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14745 : Bounds (-3170085663 / 1000000000) (-1585042829 / 500000000) (Real.log (21 / 500)) := by
  have h := reflection_log_14745_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14746_neg : (957541 / 1000000000) ≤ -Real.log (500000 / 500479) ∧
    -Real.log (500000 / 500479) ≤ (478771 / 500000000) := by
  have h := checkLog_sound (w := (479 / 1000479)) (n := 12)
    (lo := (957541 / 1000000000)) (hi := (478771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500479 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500479 / 500000) = 1/(500000 / 500479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14746 : Bounds (957541 / 1000000000) (478771 / 500000000) (Real.log (500479 / 500000)) := by
  have h := reflection_log_14746_neg
  have he : Real.log (500479 / 500000) = -Real.log (500000 / 500479) := by
    rw [show ((500479 / 500000) : ℝ) = ((500000 / 500479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14747_neg : (958459 / 1000000000) ≤ -Real.log (499521 / 500000) ∧
    -Real.log (499521 / 500000) ≤ (47923 / 50000000) := by
  have h := checkLog_sound (w := (479 / 999521)) (n := 12)
    (lo := (958459 / 1000000000)) (hi := (47923 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499521) = 1/(499521 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14747 : Bounds (-47923 / 50000000) (-958459 / 1000000000) (Real.log (499521 / 500000)) := by
  have h := reflection_log_14747_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14748_neg : (235049937 / 500000000) ≤ -Real.log (500000 / 800077) ∧
    -Real.log (500000 / 800077) ≤ (3760799 / 8000000) := by
  have h := checkLog_sound (w := (300077 / 1300077)) (n := 12)
    (lo := (235049937 / 500000000)) (hi := (3760799 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800077 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800077 / 500000) = 1/(500000 / 800077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14748 : Bounds (235049937 / 500000000) (3760799 / 8000000) (Real.log (800077 / 500000)) := by
  have h := reflection_log_14748_neg
  have he : Real.log (800077 / 500000) = -Real.log (500000 / 800077) := by
    rw [show ((800077 / 500000) : ℝ) = ((500000 / 800077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14749_neg : (183335161 / 200000000) ≤ -Real.log (199923 / 500000) ∧
    -Real.log (199923 / 500000) ≤ (916675807 / 1000000000) := by
  have h := checkLog_sound (w := (50077 / 449923)) (n := 12)
    (lo := (1788229 / 8000000)) (hi := (111764313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 199923) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 199923) = 1/(199923 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14749 : Bounds (-916675807 / 1000000000) (-183335161 / 200000000) (Real.log (199923 / 500000)) := by
  have h := reflection_log_14749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14750_neg : (235607697 / 500000000) ≤ -Real.log (50000 / 80097) ∧
    -Real.log (50000 / 80097) ≤ (94243079 / 200000000) := by
  have h := checkLog_sound (w := (30097 / 130097)) (n := 12)
    (lo := (235607697 / 500000000)) (hi := (94243079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80097 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80097 / 50000) = 1/(50000 / 80097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14750 : Bounds (235607697 / 500000000) (94243079 / 200000000) (Real.log (80097 / 50000)) := by
  have h := reflection_log_14750_neg
  have he : Real.log (80097 / 50000) = -Real.log (50000 / 80097) := by
    rw [show ((80097 / 50000) : ℝ) = ((50000 / 80097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14751_neg : (92115253 / 100000000) ≤ -Real.log (19903 / 50000) ∧
    -Real.log (19903 / 50000) ≤ (230288133 / 250000000) := by
  have h := checkLog_sound (w := (5097 / 44903)) (n := 12)
    (lo := (4560107 / 20000000)) (hi := (228005351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19903) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 19903) = 1/(19903 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14751 : Bounds (-230288133 / 250000000) (-92115253 / 100000000) (Real.log (19903 / 50000)) := by
  have h := reflection_log_14751_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14752_neg : (28121071 / 62500000) ≤ -Real.log (1594170591 / 2500000000) ∧
    -Real.log (1594170591 / 2500000000) ≤ (449937137 / 1000000000) := by
  have h := checkLog_sound (w := (905829409 / 4094170591)) (n := 12)
    (lo := (28121071 / 62500000)) (hi := (449937137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 1594170591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 1594170591) = 1/(1594170591 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14752 : Bounds (-449937137 / 1000000000) (-28121071 / 62500000) (Real.log (1594170591 / 2500000000)) := by
  have h := reflection_log_14752_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14753_neg : (446575931 / 1000000000) ≤ -Real.log (159953794071 / 250000000000) ∧
    -Real.log (159953794071 / 250000000000) ≤ (111643983 / 250000000) := by
  have h := checkLog_sound (w := (90046205929 / 409953794071)) (n := 12)
    (lo := (446575931 / 1000000000)) (hi := (111643983 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 159953794071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 159953794071) = 1/(159953794071 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14753 : Bounds (-111643983 / 250000000) (-446575931 / 1000000000) (Real.log (159953794071 / 250000000000)) := by
  have h := reflection_log_14753_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14754_neg : (1386775679 / 1000000000) ≤ -Real.log (100000000000 / 400192574141) ∧
    -Real.log (100000000000 / 400192574141) ≤ (693387841 / 500000000) := by
  have h := checkLog_sound (w := (192574141 / 800192574141)) (n := 12)
    (lo := (481319 / 1000000000)) (hi := (12033 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400192574141 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400192574141 / 400000000000) = 1/(100000000000 / 400192574141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14754 : Bounds (1386775679 / 1000000000) (693387841 / 500000000) (Real.log (400192574141 / 100000000000)) := by
  have h := reflection_log_14754_neg
  have he : Real.log (400192574141 / 100000000000) = -Real.log (100000000000 / 400192574141) := by
    rw [show ((400192574141 / 100000000000) : ℝ) = ((100000000000 / 400192574141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14755_neg : (348091981 / 250000000) ≤ -Real.log (500000000000 / 2012184092851) ∧
    -Real.log (500000000000 / 2012184092851) ≤ (1392367927 / 1000000000) := by
  have h := checkLog_sound (w := (12184092851 / 4012184092851)) (n := 12)
    (lo := (1518391 / 250000000)) (hi := (1214713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2012184092851 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2012184092851 / 2000000000000) = 1/(500000000000 / 2012184092851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14755 : Bounds (348091981 / 250000000) (1392367927 / 1000000000) (Real.log (2012184092851 / 500000000000)) := by
  have h := reflection_log_14755_neg
  have he : Real.log (2012184092851 / 500000000000) = -Real.log (500000000000 / 2012184092851) := by
    rw [show ((2012184092851 / 500000000000) : ℝ) = ((500000000000 / 2012184092851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14756_neg : (477245981 / 125000000) ≤ -Real.log (31250000000 / 1422238372093) ∧
    -Real.log (31250000000 / 1422238372093) ≤ (1908983927 / 500000000) := by
  have h := checkLog_sound (w := (422238372093 / 2422238372093)) (n := 12)
    (lo := (88057987 / 250000000)) (hi := (352231949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1422238372093 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1422238372093 / 1000000000000) = 1/(31250000000 / 1422238372093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14756 : Bounds (477245981 / 125000000) (1908983927 / 500000000) (Real.log (1422238372093 / 31250000000)) := by
  have h := reflection_log_14756_neg
  have he : Real.log (1422238372093 / 31250000000) = -Real.log (31250000000 / 1422238372093) := by
    rw [show ((1422238372093 / 31250000000) : ℝ) = ((31250000000 / 1422238372093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14757_neg : (1921004601 / 500000000) ≤ -Real.log (125000000000 / 5827380952381) ∧
    -Real.log (125000000000 / 5827380952381) ≤ (480251151 / 125000000) := by
  have h := checkLog_sound (w := (1827380952381 / 9827380952381)) (n := 12)
    (lo := (188136651 / 500000000)) (hi := (376273303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5827380952381 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5827380952381 / 4000000000000) = 1/(125000000000 / 5827380952381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14757 : Bounds (1921004601 / 500000000) (480251151 / 125000000) (Real.log (5827380952381 / 125000000000)) := by
  have h := reflection_log_14757_neg
  have he : Real.log (5827380952381 / 125000000000) = -Real.log (125000000000 / 5827380952381) := by
    rw [show ((5827380952381 / 125000000000) : ℝ) = ((125000000000 / 5827380952381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14758_neg : (336217069 / 500000000) ≤ -Real.log (1000 / 1959) ∧
    -Real.log (1000 / 1959) ≤ (672434139 / 1000000000) := by
  have h := checkLog_sound (w := (959 / 2959)) (n := 12)
    (lo := (336217069 / 500000000)) (hi := (672434139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1959 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1959 / 1000) = 1/(1000 / 1959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14758 : Bounds (336217069 / 500000000) (672434139 / 1000000000) (Real.log (1959 / 1000)) := by
  have h := reflection_log_14758_neg
  have he : Real.log (1959 / 1000) = -Real.log (1000 / 1959) := by
    rw [show ((1959 / 1000) : ℝ) = ((1000 / 1959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14759_neg : (319418321 / 100000000) ≤ -Real.log (41 / 1000) ∧
    -Real.log (41 / 1000) ≤ (638836643 / 200000000) := by
  have h := checkLog_sound (w := (43 / 207)) (n := 12)
    (lo := (42159449 / 100000000)) (hi := (421594491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 82) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 82) = 1/(41 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14759 : Bounds (-638836643 / 200000000) (-319418321 / 100000000) (Real.log (41 / 1000)) := by
  have h := reflection_log_14759_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14760_neg : (47927 / 50000000) ≤ -Real.log (1000000 / 1000959) ∧
    -Real.log (1000000 / 1000959) ≤ (958541 / 1000000000) := by
  have h := checkLog_sound (w := (959 / 2000959)) (n := 12)
    (lo := (47927 / 50000000)) (hi := (958541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000959 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000959 / 1000000) = 1/(1000000 / 1000959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14760 : Bounds (47927 / 50000000) (958541 / 1000000000) (Real.log (1000959 / 1000000)) := by
  have h := reflection_log_14760_neg
  have he : Real.log (1000959 / 1000000) = -Real.log (1000000 / 1000959) := by
    rw [show ((1000959 / 1000000) : ℝ) = ((1000000 / 1000959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14761_neg : (47973 / 50000000) ≤ -Real.log (999041 / 1000000) ∧
    -Real.log (999041 / 1000000) ≤ (959461 / 1000000000) := by
  have h := checkLog_sound (w := (959 / 1999041)) (n := 12)
    (lo := (47973 / 50000000)) (hi := (959461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999041) = 1/(999041 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14761 : Bounds (-959461 / 1000000000) (-47973 / 50000000) (Real.log (999041 / 1000000)) := by
  have h := reflection_log_14761_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14762_neg : (470805807 / 1000000000) ≤ -Real.log (250000 / 400321) ∧
    -Real.log (250000 / 400321) ≤ (29425363 / 62500000) := by
  have h := checkLog_sound (w := (150321 / 650321)) (n := 12)
    (lo := (470805807 / 1000000000)) (hi := (29425363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400321 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400321 / 250000) = 1/(250000 / 400321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14762 : Bounds (470805807 / 1000000000) (29425363 / 62500000) (Real.log (400321 / 250000)) := by
  have h := reflection_log_14762_neg
  have he : Real.log (400321 / 250000) = -Real.log (250000 / 400321) := by
    rw [show ((400321 / 250000) : ℝ) = ((250000 / 400321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14763_neg : (459752947 / 500000000) ≤ -Real.log (99679 / 250000) ∧
    -Real.log (99679 / 250000) ≤ (114938237 / 125000000) := by
  have h := checkLog_sound (w := (25321 / 224679)) (n := 12)
    (lo := (113179357 / 500000000)) (hi := (45271743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 99679) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 99679) = 1/(99679 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14763 : Bounds (-114938237 / 125000000) (-459752947 / 500000000) (Real.log (99679 / 250000)) := by
  have h := reflection_log_14763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14764_neg : (117980759 / 250000000) ≤ -Real.log (500000 / 801537) ∧
    -Real.log (500000 / 801537) ≤ (471923037 / 1000000000) := by
  have h := checkLog_sound (w := (301537 / 1301537)) (n := 12)
    (lo := (117980759 / 250000000)) (hi := (471923037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801537 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(801537 / 500000) = 1/(500000 / 801537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14764 : Bounds (117980759 / 250000000) (471923037 / 1000000000) (Real.log (801537 / 500000)) := by
  have h := reflection_log_14764_neg
  have he : Real.log (801537 / 500000) = -Real.log (500000 / 801537) := by
    rw [show ((801537 / 500000) : ℝ) = ((500000 / 801537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14765_neg : (924005413 / 1000000000) ≤ -Real.log (198463 / 500000) ∧
    -Real.log (198463 / 500000) ≤ (184801083 / 200000000) := by
  have h := checkLog_sound (w := (51537 / 448463)) (n := 12)
    (lo := (230858233 / 1000000000)) (hi := (115429117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 198463) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 198463) = 1/(198463 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14765 : Bounds (-184801083 / 200000000) (-924005413 / 1000000000) (Real.log (198463 / 500000)) := by
  have h := reflection_log_14765_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14766_neg : (452082377 / 1000000000) ≤ -Real.log (159075437631 / 250000000000) ∧
    -Real.log (159075437631 / 250000000000) ≤ (226041189 / 500000000) := by
  have h := checkLog_sound (w := (90924562369 / 409075437631)) (n := 12)
    (lo := (452082377 / 1000000000)) (hi := (226041189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 159075437631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 159075437631) = 1/(159075437631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14766 : Bounds (-226041189 / 500000000) (-452082377 / 1000000000) (Real.log (159075437631 / 250000000000)) := by
  have h := reflection_log_14766_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14767_neg : (448700087 / 1000000000) ≤ -Real.log (39903596959 / 62500000000) ∧
    -Real.log (39903596959 / 62500000000) ≤ (56087511 / 125000000) := by
  have h := checkLog_sound (w := (22596403041 / 102403596959)) (n := 12)
    (lo := (448700087 / 1000000000)) (hi := (56087511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 39903596959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 39903596959) = 1/(39903596959 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14767 : Bounds (-56087511 / 125000000) (-448700087 / 1000000000) (Real.log (39903596959 / 62500000000)) := by
  have h := reflection_log_14767_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14768_neg : (1390311701 / 1000000000) ≤ -Real.log (250000000000 / 1004025421603) ∧
    -Real.log (250000000000 / 1004025421603) ≤ (173788963 / 125000000) := by
  have h := checkLog_sound (w := (4025421603 / 2004025421603)) (n := 12)
    (lo := (4017341 / 1000000000)) (hi := (2008671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1004025421603 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1004025421603 / 1000000000000) = 1/(250000000000 / 1004025421603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14768 : Bounds (1390311701 / 1000000000) (173788963 / 125000000) (Real.log (1004025421603 / 250000000000)) := by
  have h := reflection_log_14768_neg
  have he : Real.log (1004025421603 / 250000000000) = -Real.log (250000000000 / 1004025421603) := by
    rw [show ((1004025421603 / 250000000000) : ℝ) = ((250000000000 / 1004025421603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14769_neg : (10905691 / 7812500) ≤ -Real.log (250000000000 / 1009680645763) ∧
    -Real.log (250000000000 / 1009680645763) ≤ (1395928451 / 1000000000) := by
  have h := checkLog_sound (w := (9680645763 / 2009680645763)) (n := 12)
    (lo := (1204261 / 125000000)) (hi := (9634089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1009680645763 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1009680645763 / 1000000000000) = 1/(250000000000 / 1009680645763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14769 : Bounds (10905691 / 7812500) (1395928451 / 1000000000) (Real.log (1009680645763 / 250000000000)) := by
  have h := reflection_log_14769_neg
  have he : Real.log (1009680645763 / 250000000000) = -Real.log (250000000000 / 1009680645763) := by
    rw [show ((1009680645763 / 250000000000) : ℝ) = ((250000000000 / 1009680645763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14770_neg : (1921004601 / 500000000) ≤ -Real.log (500000000000 / 23309523809523) ∧
    -Real.log (500000000000 / 23309523809523) ≤ (480251151 / 125000000) := by
  have h := checkLog_sound (w := (7309523809523 / 39309523809523)) (n := 12)
    (lo := (188136651 / 500000000)) (hi := (376273303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23309523809523 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23309523809523 / 16000000000000) = 1/(500000000000 / 23309523809523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14770 : Bounds (1921004601 / 500000000) (480251151 / 125000000) (Real.log (23309523809523 / 500000000000)) := by
  have h := reflection_log_14770_neg
  have he : Real.log (23309523809523 / 500000000000) = -Real.log (500000000000 / 23309523809523) := by
    rw [show ((23309523809523 / 500000000000) : ℝ) = ((500000000000 / 23309523809523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14771_neg : (966654337 / 250000000) ≤ -Real.log (12500000000 / 597256097561) ∧
    -Real.log (12500000000 / 597256097561) ≤ (1933308677 / 500000000) := by
  have h := checkLog_sound (w := (197256097561 / 997256097561)) (n := 12)
    (lo := (50110181 / 125000000)) (hi := (400881449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597256097561 / 400000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(597256097561 / 400000000000) = 1/(12500000000 / 597256097561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14771 : Bounds (966654337 / 250000000) (1933308677 / 500000000) (Real.log (597256097561 / 12500000000)) := by
  have h := reflection_log_14771_neg
  have he : Real.log (597256097561 / 12500000000) = -Real.log (12500000000 / 597256097561) := by
    rw [show ((597256097561 / 12500000000) : ℝ) = ((12500000000 / 597256097561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14772_neg : (672944473 / 1000000000) ≤ -Real.log (25 / 49) ∧
    -Real.log (25 / 49) ≤ (336472237 / 500000000) := by
  have h := checkLog_sound (w := (12 / 37)) (n := 12)
    (lo := (672944473 / 1000000000)) (hi := (336472237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49 / 25) = 1/(25 / 49) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14772 : Bounds (672944473 / 1000000000) (336472237 / 500000000) (Real.log (49 / 25)) := by
  have h := reflection_log_14772_neg
  have he : Real.log (49 / 25) = -Real.log (25 / 49) := by
    rw [show ((49 / 25) : ℝ) = ((25 / 49) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14773_neg : (1609437911 / 500000000) ≤ -Real.log (1 / 25) ∧
    -Real.log (1 / 25) ≤ (3218875827 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(25 / 16) = 1/(1 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14773 : Bounds (-3218875827 / 1000000000) (-1609437911 / 500000000) (Real.log (1 / 25)) := by
  have h := reflection_log_14773_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14774_neg : (959539 / 1000000000) ≤ -Real.log (3125 / 3128) ∧
    -Real.log (3125 / 3128) ≤ (47977 / 50000000) := by
  have h := checkLog_sound (w := (3 / 6253)) (n := 12)
    (lo := (959539 / 1000000000)) (hi := (47977 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3128 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3128 / 3125) = 1/(3125 / 3128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14774 : Bounds (959539 / 1000000000) (47977 / 50000000) (Real.log (3128 / 3125)) := by
  have h := reflection_log_14774_neg
  have he : Real.log (3128 / 3125) = -Real.log (3125 / 3128) := by
    rw [show ((3128 / 3125) : ℝ) = ((3125 / 3128) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14775_neg : (960461 / 1000000000) ≤ -Real.log (3122 / 3125) ∧
    -Real.log (3122 / 3125) ≤ (480231 / 500000000) := by
  have h := checkLog_sound (w := (3 / 6247)) (n := 12)
    (lo := (960461 / 1000000000)) (hi := (480231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 3122) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 3122) = 1/(3122 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14775 : Bounds (-480231 / 500000000) (-960461 / 1000000000) (Real.log (3122 / 3125)) := by
  have h := reflection_log_14775_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14776_neg : (235757181 / 500000000) ≤ -Real.log (1000000 / 1602419) ∧
    -Real.log (1000000 / 1602419) ≤ (471514363 / 1000000000) := by
  have h := checkLog_sound (w := (602419 / 2602419)) (n := 12)
    (lo := (235757181 / 500000000)) (hi := (471514363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1602419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1602419 / 1000000) = 1/(1000000 / 1602419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14776 : Bounds (235757181 / 500000000) (471514363 / 1000000000) (Real.log (1602419 / 1000000)) := by
  have h := reflection_log_14776_neg
  have he : Real.log (1602419 / 1000000) = -Real.log (1000000 / 1602419) := by
    rw [show ((1602419 / 1000000) : ℝ) = ((1000000 / 1602419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14777_neg : (922356591 / 1000000000) ≤ -Real.log (397581 / 1000000) ∧
    -Real.log (397581 / 1000000) ≤ (922356593 / 1000000000) := by
  have h := checkLog_sound (w := (102419 / 897581)) (n := 12)
    (lo := (229209411 / 1000000000)) (hi := (57302353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 397581) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 397581) = 1/(397581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14777 : Bounds (-922356593 / 1000000000) (-922356591 / 1000000000) (Real.log (397581 / 1000000)) := by
  have h := reflection_log_14777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14778_neg : (23631727 / 50000000) ≤ -Real.log (200000 / 320843) ∧
    -Real.log (200000 / 320843) ≤ (472634541 / 1000000000) := by
  have h := checkLog_sound (w := (120843 / 520843)) (n := 12)
    (lo := (23631727 / 50000000)) (hi := (472634541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320843 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320843 / 200000) = 1/(200000 / 320843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14778 : Bounds (23631727 / 50000000) (472634541 / 1000000000) (Real.log (320843 / 200000)) := by
  have h := reflection_log_14778_neg
  have he : Real.log (320843 / 200000) = -Real.log (200000 / 320843) := by
    rw [show ((320843 / 200000) : ℝ) = ((200000 / 320843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14779_neg : (926884143 / 1000000000) ≤ -Real.log (79157 / 200000) ∧
    -Real.log (79157 / 200000) ≤ (185376829 / 200000000) := by
  have h := checkLog_sound (w := (20843 / 179157)) (n := 12)
    (lo := (233736963 / 1000000000)) (hi := (58434241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 79157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 79157) = 1/(79157 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14779 : Bounds (-185376829 / 200000000) (-926884143 / 1000000000) (Real.log (79157 / 200000)) := by
  have h := reflection_log_14779_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14780_neg : (113562401 / 250000000) ≤ -Real.log (25396969351 / 40000000000) ∧
    -Real.log (25396969351 / 40000000000) ≤ (90849921 / 200000000) := by
  have h := checkLog_sound (w := (14603030649 / 65396969351)) (n := 12)
    (lo := (113562401 / 250000000)) (hi := (90849921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 25396969351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 25396969351) = 1/(25396969351 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14780 : Bounds (-90849921 / 200000000) (-113562401 / 250000000) (Real.log (25396969351 / 40000000000)) := by
  have h := reflection_log_14780_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14781_neg : (450842229 / 1000000000) ≤ -Real.log (637091348439 / 1000000000000) ∧
    -Real.log (637091348439 / 1000000000000) ≤ (45084223 / 100000000) := by
  have h := checkLog_sound (w := (362908651561 / 1637091348439)) (n := 12)
    (lo := (450842229 / 1000000000)) (hi := (45084223 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 637091348439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 637091348439) = 1/(637091348439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14781 : Bounds (-45084223 / 100000000) (-450842229 / 1000000000) (Real.log (637091348439 / 1000000000000)) := by
  have h := reflection_log_14781_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14782_neg : (1393870953 / 1000000000) ≤ -Real.log (500000000000 / 2015210736931) ∧
    -Real.log (500000000000 / 2015210736931) ≤ (348467739 / 250000000) := by
  have h := checkLog_sound (w := (15210736931 / 4015210736931)) (n := 12)
    (lo := (7576593 / 1000000000)) (hi := (3788297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2015210736931 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2015210736931 / 2000000000000) = 1/(500000000000 / 2015210736931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14782 : Bounds (1393870953 / 1000000000) (348467739 / 250000000) (Real.log (2015210736931 / 500000000000)) := by
  have h := reflection_log_14782_neg
  have he : Real.log (2015210736931 / 500000000000) = -Real.log (500000000000 / 2015210736931) := by
    rw [show ((2015210736931 / 500000000000) : ℝ) = ((500000000000 / 2015210736931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14783_neg : (1399518683 / 1000000000) ≤ -Real.log (1250000000 / 5066560759) ∧
    -Real.log (1250000000 / 5066560759) ≤ (699759343 / 500000000) := by
  have h := checkLog_sound (w := (66560759 / 10066560759)) (n := 12)
    (lo := (13224323 / 1000000000)) (hi := (3306081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5066560759 / 5000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(5066560759 / 5000000000) = 1/(1250000000 / 5066560759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14783 : Bounds (1399518683 / 1000000000) (699759343 / 500000000) (Real.log (5066560759 / 1250000000)) := by
  have h := reflection_log_14783_neg
  have he : Real.log (5066560759 / 1250000000) = -Real.log (1250000000 / 5066560759) := by
    rw [show ((5066560759 / 1250000000) : ℝ) = ((1250000000 / 5066560759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
