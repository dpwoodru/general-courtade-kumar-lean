import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8704_neg : (268254609 / 500000000) ≤ -Real.log (62500000000 / 106876693767) ∧
    -Real.log (62500000000 / 106876693767) ≤ (536509219 / 1000000000) := by
  have h := checkLog_sound (w := (44376693767 / 169376693767)) (n := 12)
    (lo := (268254609 / 500000000)) (hi := (536509219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106876693767 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106876693767 / 62500000000) = 1/(62500000000 / 106876693767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8704 : Bounds (268254609 / 500000000) (536509219 / 1000000000) (Real.log (106876693767 / 62500000000)) := by
  have h := reflection_log_8704_neg
  have he : Real.log (106876693767 / 62500000000) = -Real.log (62500000000 / 106876693767) := by
    rw [show ((106876693767 / 62500000000) : ℝ) = ((62500000000 / 106876693767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8705_neg : (116546941 / 500000000) ≤ -Real.log (80 / 101) ∧
    -Real.log (80 / 101) ≤ (233093883 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 181)) (n := 12)
    (lo := (116546941 / 500000000)) (hi := (233093883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101 / 80) = 1/(80 / 101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8705 : Bounds (116546941 / 500000000) (233093883 / 1000000000) (Real.log (101 / 80)) := by
  have h := reflection_log_8705_neg
  have he : Real.log (101 / 80) = -Real.log (80 / 101) := by
    rw [show ((101 / 80) : ℝ) = ((80 / 101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8706_neg : (30448919 / 100000000) ≤ -Real.log (59 / 80) ∧
    -Real.log (59 / 80) ≤ (304489191 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 139)) (n := 12)
    (lo := (30448919 / 100000000)) (hi := (304489191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 59) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 59) = 1/(59 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8706 : Bounds (-304489191 / 1000000000) (-30448919 / 100000000) (Real.log (59 / 80)) := by
  have h := reflection_log_8706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8707_neg : (52493 / 200000000) ≤ -Real.log (80000 / 80021) ∧
    -Real.log (80000 / 80021) ≤ (131233 / 500000000) := by
  have h := checkLog_sound (w := (21 / 160021)) (n := 12)
    (lo := (52493 / 200000000)) (hi := (131233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80021 / 80000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80021 / 80000) = 1/(80000 / 80021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8707 : Bounds (52493 / 200000000) (131233 / 500000000) (Real.log (80021 / 80000)) := by
  have h := reflection_log_8707_neg
  have he : Real.log (80021 / 80000) = -Real.log (80000 / 80021) := by
    rw [show ((80021 / 80000) : ℝ) = ((80000 / 80021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8708_neg : (131267 / 500000000) ≤ -Real.log (79979 / 80000) ∧
    -Real.log (79979 / 80000) ≤ (52507 / 200000000) := by
  have h := checkLog_sound (w := (21 / 159979)) (n := 12)
    (lo := (131267 / 500000000)) (hi := (52507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80000 / 79979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80000 / 79979) = 1/(79979 / 80000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8708 : Bounds (-52507 / 200000000) (-131267 / 500000000) (Real.log (79979 / 80000)) := by
  have h := reflection_log_8708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8709_neg : (62454349 / 500000000) ≤ -Real.log (200000 / 226609) ∧
    -Real.log (200000 / 226609) ≤ (124908699 / 1000000000) := by
  have h := checkLog_sound (w := (26609 / 426609)) (n := 12)
    (lo := (62454349 / 500000000)) (hi := (124908699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226609 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226609 / 200000) = 1/(200000 / 226609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8709 : Bounds (62454349 / 500000000) (124908699 / 1000000000) (Real.log (226609 / 200000)) := by
  have h := reflection_log_8709_neg
  have he : Real.log (226609 / 200000) = -Real.log (200000 / 226609) := by
    rw [show ((226609 / 200000) : ℝ) = ((200000 / 226609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8710_neg : (71384103 / 500000000) ≤ -Real.log (173391 / 200000) ∧
    -Real.log (173391 / 200000) ≤ (142768207 / 1000000000) := by
  have h := checkLog_sound (w := (26609 / 373391)) (n := 12)
    (lo := (71384103 / 500000000)) (hi := (142768207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173391) = 1/(173391 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8710 : Bounds (-142768207 / 1000000000) (-71384103 / 500000000) (Real.log (173391 / 200000)) := by
  have h := reflection_log_8710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8711_neg : (17859507 / 1000000000) ≤ -Real.log (39291961119 / 40000000000) ∧
    -Real.log (39291961119 / 40000000000) ≤ (4464877 / 250000000) := by
  have h := checkLog_sound (w := (708038881 / 79291961119)) (n := 12)
    (lo := (17859507 / 1000000000)) (hi := (4464877 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39291961119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39291961119) = 1/(39291961119 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8711 : Bounds (-4464877 / 250000000) (-17859507 / 1000000000) (Real.log (39291961119 / 40000000000)) := by
  have h := reflection_log_8711_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8712_neg : (266618239 / 1000000000) ≤ -Real.log (250000000000 / 326385486613) ∧
    -Real.log (250000000000 / 326385486613) ≤ (416591 / 1562500) := by
  have h := checkLog_sound (w := (76385486613 / 576385486613)) (n := 12)
    (lo := (266618239 / 1000000000)) (hi := (416591 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326385486613 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326385486613 / 250000000000) = 1/(250000000000 / 326385486613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8712 : Bounds (266618239 / 1000000000) (416591 / 1562500) (Real.log (326385486613 / 250000000000)) := by
  have h := reflection_log_8712_neg
  have he : Real.log (326385486613 / 250000000000) = -Real.log (250000000000 / 326385486613) := by
    rw [show ((326385486613 / 250000000000) : ℝ) = ((250000000000 / 326385486613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8713_neg : (53535381 / 200000000) ≤ -Real.log (500000000000 / 653462405777) ∧
    -Real.log (500000000000 / 653462405777) ≤ (133838453 / 500000000) := by
  have h := checkLog_sound (w := (153462405777 / 1153462405777)) (n := 12)
    (lo := (53535381 / 200000000)) (hi := (133838453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((653462405777 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(653462405777 / 500000000000) = 1/(500000000000 / 653462405777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8713 : Bounds (53535381 / 200000000) (133838453 / 500000000) (Real.log (653462405777 / 500000000000)) := by
  have h := reflection_log_8713_neg
  have he : Real.log (653462405777 / 500000000000) = -Real.log (500000000000 / 653462405777) := by
    rw [show ((653462405777 / 500000000000) : ℝ) = ((500000000000 / 653462405777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8714_neg : (268254609 / 500000000) ≤ -Real.log (100000000000 / 171002710027) ∧
    -Real.log (100000000000 / 171002710027) ≤ (536509219 / 1000000000) := by
  have h := checkLog_sound (w := (71002710027 / 271002710027)) (n := 12)
    (lo := (268254609 / 500000000)) (hi := (536509219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171002710027 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171002710027 / 100000000000) = 1/(100000000000 / 171002710027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8714 : Bounds (268254609 / 500000000) (536509219 / 1000000000) (Real.log (171002710027 / 100000000000)) := by
  have h := reflection_log_8714_neg
  have he : Real.log (171002710027 / 100000000000) = -Real.log (100000000000 / 171002710027) := by
    rw [show ((171002710027 / 100000000000) : ℝ) = ((100000000000 / 171002710027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8715_neg : (16799471 / 31250000) ≤ -Real.log (50000000000 / 85593220339) ∧
    -Real.log (50000000000 / 85593220339) ≤ (537583073 / 1000000000) := by
  have h := checkLog_sound (w := (35593220339 / 135593220339)) (n := 12)
    (lo := (16799471 / 31250000)) (hi := (537583073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85593220339 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85593220339 / 50000000000) = 1/(50000000000 / 85593220339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8715 : Bounds (16799471 / 31250000) (537583073 / 1000000000) (Real.log (85593220339 / 50000000000)) := by
  have h := reflection_log_8715_neg
  have he : Real.log (85593220339 / 50000000000) = -Real.log (50000000000 / 85593220339) := by
    rw [show ((85593220339 / 50000000000) : ℝ) = ((50000000000 / 85593220339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8716_neg : (233489843 / 1000000000) ≤ -Real.log (1000 / 1263) ∧
    -Real.log (1000 / 1263) ≤ (58372461 / 250000000) := by
  have h := checkLog_sound (w := (263 / 2263)) (n := 12)
    (lo := (233489843 / 1000000000)) (hi := (58372461 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1263 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1263 / 1000) = 1/(1000 / 1263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8716 : Bounds (233489843 / 1000000000) (58372461 / 250000000) (Real.log (1263 / 1000)) := by
  have h := reflection_log_8716_neg
  have he : Real.log (1263 / 1000) = -Real.log (1000 / 1263) := by
    rw [show ((1263 / 1000) : ℝ) = ((1000 / 1263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8717_neg : (152583693 / 500000000) ≤ -Real.log (737 / 1000) ∧
    -Real.log (737 / 1000) ≤ (305167387 / 1000000000) := by
  have h := checkLog_sound (w := (263 / 1737)) (n := 12)
    (lo := (152583693 / 500000000)) (hi := (305167387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 737) = 1/(737 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8717 : Bounds (-305167387 / 1000000000) (-152583693 / 500000000) (Real.log (737 / 1000)) := by
  have h := reflection_log_8717_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8718_neg : (52593 / 200000000) ≤ -Real.log (1000000 / 1000263) ∧
    -Real.log (1000000 / 1000263) ≤ (131483 / 500000000) := by
  have h := checkLog_sound (w := (263 / 2000263)) (n := 12)
    (lo := (52593 / 200000000)) (hi := (131483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000263 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000263 / 1000000) = 1/(1000000 / 1000263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8718 : Bounds (52593 / 200000000) (131483 / 500000000) (Real.log (1000263 / 1000000)) := by
  have h := reflection_log_8718_neg
  have he : Real.log (1000263 / 1000000) = -Real.log (1000000 / 1000263) := by
    rw [show ((1000263 / 1000000) : ℝ) = ((1000000 / 1000263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8719_neg : (131517 / 500000000) ≤ -Real.log (999737 / 1000000) ∧
    -Real.log (999737 / 1000000) ≤ (52607 / 200000000) := by
  have h := checkLog_sound (w := (263 / 1999737)) (n := 12)
    (lo := (131517 / 500000000)) (hi := (52607 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999737) = 1/(999737 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8719 : Bounds (-52607 / 200000000) (-131517 / 500000000) (Real.log (999737 / 1000000)) := by
  have h := reflection_log_8719_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8720_neg : (62569071 / 500000000) ≤ -Real.log (200000 / 226661) ∧
    -Real.log (200000 / 226661) ≤ (125138143 / 1000000000) := by
  have h := checkLog_sound (w := (26661 / 426661)) (n := 12)
    (lo := (62569071 / 500000000)) (hi := (125138143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226661 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226661 / 200000) = 1/(200000 / 226661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8720 : Bounds (62569071 / 500000000) (125138143 / 1000000000) (Real.log (226661 / 200000)) := by
  have h := reflection_log_8720_neg
  have he : Real.log (226661 / 200000) = -Real.log (200000 / 226661) := by
    rw [show ((226661 / 200000) : ℝ) = ((200000 / 226661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8721_neg : (143068151 / 1000000000) ≤ -Real.log (173339 / 200000) ∧
    -Real.log (173339 / 200000) ≤ (17883519 / 125000000) := by
  have h := checkLog_sound (w := (26661 / 373339)) (n := 12)
    (lo := (143068151 / 1000000000)) (hi := (17883519 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173339) = 1/(173339 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8721 : Bounds (-17883519 / 125000000) (-143068151 / 1000000000) (Real.log (173339 / 200000)) := by
  have h := reflection_log_8721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8722_neg : (17930009 / 1000000000) ≤ -Real.log (39289191079 / 40000000000) ∧
    -Real.log (39289191079 / 40000000000) ≤ (1793001 / 100000000) := by
  have h := checkLog_sound (w := (710808921 / 79289191079)) (n := 12)
    (lo := (17930009 / 1000000000)) (hi := (1793001 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39289191079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39289191079) = 1/(39289191079 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8722 : Bounds (-1793001 / 100000000) (-17930009 / 1000000000) (Real.log (39289191079 / 40000000000)) := by
  have h := reflection_log_8722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8723_neg : (267147553 / 1000000000) ≤ -Real.log (125000000000 / 163279146463) ∧
    -Real.log (125000000000 / 163279146463) ≤ (133573777 / 500000000) := by
  have h := checkLog_sound (w := (38279146463 / 288279146463)) (n := 12)
    (lo := (267147553 / 1000000000)) (hi := (133573777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163279146463 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163279146463 / 125000000000) = 1/(125000000000 / 163279146463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8723 : Bounds (267147553 / 1000000000) (133573777 / 500000000) (Real.log (163279146463 / 125000000000)) := by
  have h := reflection_log_8723_neg
  have he : Real.log (163279146463 / 125000000000) = -Real.log (125000000000 / 163279146463) := by
    rw [show ((163279146463 / 125000000000) : ℝ) = ((125000000000 / 163279146463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8724_neg : (134103147 / 500000000) ≤ -Real.log (250000000000 / 326904216593) ∧
    -Real.log (250000000000 / 326904216593) ≤ (53641259 / 200000000) := by
  have h := checkLog_sound (w := (76904216593 / 576904216593)) (n := 12)
    (lo := (134103147 / 500000000)) (hi := (53641259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326904216593 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326904216593 / 250000000000) = 1/(250000000000 / 326904216593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8724 : Bounds (134103147 / 500000000) (53641259 / 200000000) (Real.log (326904216593 / 250000000000)) := by
  have h := reflection_log_8724_neg
  have he : Real.log (326904216593 / 250000000000) = -Real.log (250000000000 / 326904216593) := by
    rw [show ((326904216593 / 250000000000) : ℝ) = ((250000000000 / 326904216593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8725_neg : (16799471 / 31250000) ≤ -Real.log (500000000000 / 855932203389) ∧
    -Real.log (500000000000 / 855932203389) ≤ (537583073 / 1000000000) := by
  have h := checkLog_sound (w := (355932203389 / 1355932203389)) (n := 12)
    (lo := (16799471 / 31250000)) (hi := (537583073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((855932203389 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(855932203389 / 500000000000) = 1/(500000000000 / 855932203389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8725 : Bounds (16799471 / 31250000) (537583073 / 1000000000) (Real.log (855932203389 / 500000000000)) := by
  have h := reflection_log_8725_neg
  have he : Real.log (855932203389 / 500000000000) = -Real.log (500000000000 / 855932203389) := by
    rw [show ((855932203389 / 500000000000) : ℝ) = ((500000000000 / 855932203389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8726_neg : (53865723 / 100000000) ≤ -Real.log (500000000000 / 856852103121) ∧
    -Real.log (500000000000 / 856852103121) ≤ (538657231 / 1000000000) := by
  have h := checkLog_sound (w := (356852103121 / 1356852103121)) (n := 12)
    (lo := (53865723 / 100000000)) (hi := (538657231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((856852103121 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(856852103121 / 500000000000) = 1/(500000000000 / 856852103121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8726 : Bounds (53865723 / 100000000) (538657231 / 1000000000) (Real.log (856852103121 / 500000000000)) := by
  have h := reflection_log_8726_neg
  have he : Real.log (856852103121 / 500000000000) = -Real.log (500000000000 / 856852103121) := by
    rw [show ((856852103121 / 500000000000) : ℝ) = ((500000000000 / 856852103121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8727_neg : (233885647 / 1000000000) ≤ -Real.log (2000 / 2527) ∧
    -Real.log (2000 / 2527) ≤ (14617853 / 62500000) := by
  have h := checkLog_sound (w := (527 / 4527)) (n := 12)
    (lo := (233885647 / 1000000000)) (hi := (14617853 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2527 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2527 / 2000) = 1/(2000 / 2527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8727 : Bounds (233885647 / 1000000000) (14617853 / 62500000) (Real.log (2527 / 2000)) := by
  have h := reflection_log_8727_neg
  have he : Real.log (2527 / 2000) = -Real.log (2000 / 2527) := by
    rw [show ((2527 / 2000) : ℝ) = ((2000 / 2527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8728_neg : (305846043 / 1000000000) ≤ -Real.log (1473 / 2000) ∧
    -Real.log (1473 / 2000) ≤ (76461511 / 250000000) := by
  have h := checkLog_sound (w := (527 / 3473)) (n := 12)
    (lo := (305846043 / 1000000000)) (hi := (76461511 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1473) = 1/(1473 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8728 : Bounds (-76461511 / 250000000) (-305846043 / 1000000000) (Real.log (1473 / 2000)) := by
  have h := reflection_log_8728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8729_neg : (52693 / 200000000) ≤ -Real.log (2000000 / 2000527) ∧
    -Real.log (2000000 / 2000527) ≤ (131733 / 500000000) := by
  have h := checkLog_sound (w := (527 / 4000527)) (n := 12)
    (lo := (52693 / 200000000)) (hi := (131733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000527 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000527 / 2000000) = 1/(2000000 / 2000527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8729 : Bounds (52693 / 200000000) (131733 / 500000000) (Real.log (2000527 / 2000000)) := by
  have h := reflection_log_8729_neg
  have he : Real.log (2000527 / 2000000) = -Real.log (2000000 / 2000527) := by
    rw [show ((2000527 / 2000000) : ℝ) = ((2000000 / 2000527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8730_neg : (131767 / 500000000) ≤ -Real.log (1999473 / 2000000) ∧
    -Real.log (1999473 / 2000000) ≤ (52707 / 200000000) := by
  have h := checkLog_sound (w := (527 / 3999473)) (n := 12)
    (lo := (131767 / 500000000)) (hi := (52707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999473) = 1/(1999473 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8730 : Bounds (-52707 / 200000000) (-131767 / 500000000) (Real.log (1999473 / 2000000)) := by
  have h := reflection_log_8730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8731_neg : (15613477 / 125000000) ≤ -Real.log (250000 / 283261) ∧
    -Real.log (250000 / 283261) ≤ (124907817 / 1000000000) := by
  have h := checkLog_sound (w := (33261 / 533261)) (n := 12)
    (lo := (15613477 / 125000000)) (hi := (124907817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((283261 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(283261 / 250000) = 1/(250000 / 283261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8731 : Bounds (15613477 / 125000000) (124907817 / 1000000000) (Real.log (283261 / 250000)) := by
  have h := reflection_log_8731_neg
  have he : Real.log (283261 / 250000) = -Real.log (250000 / 283261) := by
    rw [show ((283261 / 250000) : ℝ) = ((250000 / 283261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8732_neg : (142767053 / 1000000000) ≤ -Real.log (216739 / 250000) ∧
    -Real.log (216739 / 250000) ≤ (71383527 / 500000000) := by
  have h := checkLog_sound (w := (33261 / 466739)) (n := 12)
    (lo := (142767053 / 1000000000)) (hi := (71383527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 216739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 216739) = 1/(216739 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8732 : Bounds (-71383527 / 500000000) (-142767053 / 1000000000) (Real.log (216739 / 250000)) := by
  have h := reflection_log_8732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8733_neg : (125367533 / 1000000000) ≤ -Real.log (200000 / 226713) ∧
    -Real.log (200000 / 226713) ≤ (62683767 / 500000000) := by
  have h := checkLog_sound (w := (26713 / 426713)) (n := 12)
    (lo := (125367533 / 1000000000)) (hi := (62683767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226713 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226713 / 200000) = 1/(200000 / 226713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8733 : Bounds (125367533 / 1000000000) (62683767 / 500000000) (Real.log (226713 / 200000)) := by
  have h := reflection_log_8733_neg
  have he : Real.log (226713 / 200000) = -Real.log (200000 / 226713) := by
    rw [show ((226713 / 200000) : ℝ) = ((200000 / 226713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8734_neg : (143368187 / 1000000000) ≤ -Real.log (173287 / 200000) ∧
    -Real.log (173287 / 200000) ≤ (35842047 / 250000000) := by
  have h := checkLog_sound (w := (26713 / 373287)) (n := 12)
    (lo := (143368187 / 1000000000)) (hi := (35842047 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173287) = 1/(173287 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8734 : Bounds (-35842047 / 250000000) (-143368187 / 1000000000) (Real.log (173287 / 200000)) := by
  have h := reflection_log_8734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8735_neg : (18000653 / 1000000000) ≤ -Real.log (39286415631 / 40000000000) ∧
    -Real.log (39286415631 / 40000000000) ≤ (9000327 / 500000000) := by
  have h := checkLog_sound (w := (713584369 / 79286415631)) (n := 12)
    (lo := (18000653 / 1000000000)) (hi := (9000327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39286415631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39286415631) = 1/(39286415631 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8735 : Bounds (-9000327 / 500000000) (-18000653 / 1000000000) (Real.log (39286415631 / 40000000000)) := by
  have h := reflection_log_8735_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8736_neg : (4464809 / 250000000) ≤ -Real.log (61393705879 / 62500000000) ∧
    -Real.log (61393705879 / 62500000000) ≤ (17859237 / 1000000000) := by
  have h := checkLog_sound (w := (1106294121 / 123893705879)) (n := 12)
    (lo := (4464809 / 250000000)) (hi := (17859237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61393705879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61393705879) = 1/(61393705879 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8736 : Bounds (-17859237 / 1000000000) (-4464809 / 250000000) (Real.log (61393705879 / 62500000000)) := by
  have h := reflection_log_8736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8737_neg : (267674869 / 1000000000) ≤ -Real.log (250000000000 / 326730537651) ∧
    -Real.log (250000000000 / 326730537651) ≤ (26767487 / 100000000) := by
  have h := checkLog_sound (w := (76730537651 / 576730537651)) (n := 12)
    (lo := (267674869 / 1000000000)) (hi := (26767487 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326730537651 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326730537651 / 250000000000) = 1/(250000000000 / 326730537651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8737 : Bounds (267674869 / 1000000000) (26767487 / 100000000) (Real.log (326730537651 / 250000000000)) := by
  have h := reflection_log_8737_neg
  have he : Real.log (326730537651 / 250000000000) = -Real.log (250000000000 / 326730537651) := by
    rw [show ((326730537651 / 250000000000) : ℝ) = ((250000000000 / 326730537651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8738_neg : (6718393 / 25000000) ≤ -Real.log (125000000000 / 163538667067) ∧
    -Real.log (125000000000 / 163538667067) ≤ (268735721 / 1000000000) := by
  have h := checkLog_sound (w := (38538667067 / 288538667067)) (n := 12)
    (lo := (6718393 / 25000000)) (hi := (268735721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163538667067 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163538667067 / 125000000000) = 1/(125000000000 / 163538667067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8738 : Bounds (6718393 / 25000000) (268735721 / 1000000000) (Real.log (163538667067 / 125000000000)) := by
  have h := reflection_log_8738_neg
  have he : Real.log (163538667067 / 125000000000) = -Real.log (125000000000 / 163538667067) := by
    rw [show ((163538667067 / 125000000000) : ℝ) = ((125000000000 / 163538667067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8739_neg : (53865723 / 100000000) ≤ -Real.log (6250000000 / 10710651289) ∧
    -Real.log (6250000000 / 10710651289) ≤ (538657231 / 1000000000) := by
  have h := checkLog_sound (w := (4460651289 / 16960651289)) (n := 12)
    (lo := (53865723 / 100000000)) (hi := (538657231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10710651289 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10710651289 / 6250000000) = 1/(6250000000 / 10710651289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8739 : Bounds (53865723 / 100000000) (538657231 / 1000000000) (Real.log (10710651289 / 6250000000)) := by
  have h := reflection_log_8739_neg
  have he : Real.log (10710651289 / 6250000000) = -Real.log (6250000000 / 10710651289) := by
    rw [show ((10710651289 / 6250000000) : ℝ) = ((6250000000 / 10710651289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8740_neg : (53973169 / 100000000) ≤ -Real.log (500000000000 / 857773251867) ∧
    -Real.log (500000000000 / 857773251867) ≤ (539731691 / 1000000000) := by
  have h := checkLog_sound (w := (357773251867 / 1357773251867)) (n := 12)
    (lo := (53973169 / 100000000)) (hi := (539731691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((857773251867 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(857773251867 / 500000000000) = 1/(500000000000 / 857773251867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8740 : Bounds (53973169 / 100000000) (539731691 / 1000000000) (Real.log (857773251867 / 500000000000)) := by
  have h := reflection_log_8740_neg
  have he : Real.log (857773251867 / 500000000000) = -Real.log (500000000000 / 857773251867) := by
    rw [show ((857773251867 / 500000000000) : ℝ) = ((500000000000 / 857773251867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8741_neg : (46856259 / 200000000) ≤ -Real.log (125 / 158) ∧
    -Real.log (125 / 158) ≤ (14642581 / 62500000) := by
  have h := checkLog_sound (w := (33 / 283)) (n := 12)
    (lo := (46856259 / 200000000)) (hi := (14642581 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158 / 125) = 1/(125 / 158) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8741 : Bounds (46856259 / 200000000) (14642581 / 62500000) (Real.log (158 / 125)) := by
  have h := reflection_log_8741_neg
  have he : Real.log (158 / 125) = -Real.log (125 / 158) := by
    rw [show ((158 / 125) : ℝ) = ((125 / 158) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8742_neg : (7663129 / 25000000) ≤ -Real.log (92 / 125) ∧
    -Real.log (92 / 125) ≤ (306525161 / 1000000000) := by
  have h := checkLog_sound (w := (33 / 217)) (n := 12)
    (lo := (7663129 / 25000000)) (hi := (306525161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 92) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 92) = 1/(92 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8742 : Bounds (-306525161 / 1000000000) (-7663129 / 25000000) (Real.log (92 / 125)) := by
  have h := reflection_log_8742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8743_neg : (52793 / 200000000) ≤ -Real.log (125000 / 125033) ∧
    -Real.log (125000 / 125033) ≤ (131983 / 500000000) := by
  have h := checkLog_sound (w := (33 / 250033)) (n := 12)
    (lo := (52793 / 200000000)) (hi := (131983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125033 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125033 / 125000) = 1/(125000 / 125033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8743 : Bounds (52793 / 200000000) (131983 / 500000000) (Real.log (125033 / 125000)) := by
  have h := reflection_log_8743_neg
  have he : Real.log (125033 / 125000) = -Real.log (125000 / 125033) := by
    rw [show ((125033 / 125000) : ℝ) = ((125000 / 125033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8744_neg : (132017 / 500000000) ≤ -Real.log (124967 / 125000) ∧
    -Real.log (124967 / 125000) ≤ (52807 / 200000000) := by
  have h := checkLog_sound (w := (33 / 249967)) (n := 12)
    (lo := (132017 / 500000000)) (hi := (52807 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124967) = 1/(124967 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8744 : Bounds (-52807 / 200000000) (-132017 / 500000000) (Real.log (124967 / 125000)) := by
  have h := reflection_log_8744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8745_neg : (6256863 / 50000000) ≤ -Real.log (125000 / 141663) ∧
    -Real.log (125000 / 141663) ≤ (125137261 / 1000000000) := by
  have h := checkLog_sound (w := (16663 / 266663)) (n := 12)
    (lo := (6256863 / 50000000)) (hi := (125137261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141663 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141663 / 125000) = 1/(125000 / 141663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8745 : Bounds (6256863 / 50000000) (125137261 / 1000000000) (Real.log (141663 / 125000)) := by
  have h := reflection_log_8745_neg
  have he : Real.log (141663 / 125000) = -Real.log (125000 / 141663) := by
    rw [show ((141663 / 125000) : ℝ) = ((125000 / 141663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8746_neg : (71533499 / 500000000) ≤ -Real.log (108337 / 125000) ∧
    -Real.log (108337 / 125000) ≤ (143066999 / 1000000000) := by
  have h := checkLog_sound (w := (16663 / 233337)) (n := 12)
    (lo := (71533499 / 500000000)) (hi := (143066999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 108337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 108337) = 1/(108337 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8746 : Bounds (-143066999 / 1000000000) (-71533499 / 500000000) (Real.log (108337 / 125000)) := by
  have h := reflection_log_8746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8747_neg : (15699609 / 125000000) ≤ -Real.log (40000 / 45353) ∧
    -Real.log (40000 / 45353) ≤ (125596873 / 1000000000) := by
  have h := checkLog_sound (w := (5353 / 85353)) (n := 12)
    (lo := (15699609 / 125000000)) (hi := (125596873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45353 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45353 / 40000) = 1/(40000 / 45353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8747 : Bounds (15699609 / 125000000) (125596873 / 1000000000) (Real.log (45353 / 40000)) := by
  have h := reflection_log_8747_neg
  have he : Real.log (45353 / 40000) = -Real.log (40000 / 45353) := by
    rw [show ((45353 / 40000) : ℝ) = ((40000 / 45353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8748_neg : (17958539 / 125000000) ≤ -Real.log (34647 / 40000) ∧
    -Real.log (34647 / 40000) ≤ (143668313 / 1000000000) := by
  have h := checkLog_sound (w := (5353 / 74647)) (n := 12)
    (lo := (17958539 / 125000000)) (hi := (143668313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 34647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 34647) = 1/(34647 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8748 : Bounds (-143668313 / 1000000000) (-17958539 / 125000000) (Real.log (34647 / 40000)) := by
  have h := reflection_log_8748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8749_neg : (18071439 / 1000000000) ≤ -Real.log (1571345391 / 1600000000) ∧
    -Real.log (1571345391 / 1600000000) ≤ (225893 / 12500000) := by
  have h := checkLog_sound (w := (28654609 / 3171345391)) (n := 12)
    (lo := (18071439 / 1000000000)) (hi := (225893 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1571345391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1571345391) = 1/(1571345391 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8749 : Bounds (-225893 / 12500000) (-18071439 / 1000000000) (Real.log (1571345391 / 1600000000)) := by
  have h := reflection_log_8749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8750_neg : (17929737 / 1000000000) ≤ -Real.log (15347344431 / 15625000000) ∧
    -Real.log (15347344431 / 15625000000) ≤ (8964869 / 500000000) := by
  have h := checkLog_sound (w := (277655569 / 30972344431)) (n := 12)
    (lo := (17929737 / 1000000000)) (hi := (8964869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15347344431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15347344431) = 1/(15347344431 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8750 : Bounds (-8964869 / 500000000) (-17929737 / 1000000000) (Real.log (15347344431 / 15625000000)) := by
  have h := reflection_log_8750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8751_neg : (134102129 / 500000000) ≤ -Real.log (500000000000 / 653807101913) ∧
    -Real.log (500000000000 / 653807101913) ≤ (268204259 / 1000000000) := by
  have h := checkLog_sound (w := (153807101913 / 1153807101913)) (n := 12)
    (lo := (134102129 / 500000000)) (hi := (268204259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((653807101913 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(653807101913 / 500000000000) = 1/(500000000000 / 653807101913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8751 : Bounds (134102129 / 500000000) (268204259 / 1000000000) (Real.log (653807101913 / 500000000000)) := by
  have h := reflection_log_8751_neg
  have he : Real.log (653807101913 / 500000000000) = -Real.log (500000000000 / 653807101913) := by
    rw [show ((653807101913 / 500000000000) : ℝ) = ((500000000000 / 653807101913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8752_neg : (8414537 / 31250000) ≤ -Real.log (62500000000 / 81812638901) ∧
    -Real.log (62500000000 / 81812638901) ≤ (53853037 / 200000000) := by
  have h := checkLog_sound (w := (19312638901 / 144312638901)) (n := 12)
    (lo := (8414537 / 31250000)) (hi := (53853037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81812638901 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81812638901 / 62500000000) = 1/(62500000000 / 81812638901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8752 : Bounds (8414537 / 31250000) (53853037 / 200000000) (Real.log (81812638901 / 62500000000)) := by
  have h := reflection_log_8752_neg
  have he : Real.log (81812638901 / 62500000000) = -Real.log (62500000000 / 81812638901) := by
    rw [show ((81812638901 / 62500000000) : ℝ) = ((62500000000 / 81812638901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8753_neg : (53973169 / 100000000) ≤ -Real.log (250000000000 / 428886625933) ∧
    -Real.log (250000000000 / 428886625933) ≤ (539731691 / 1000000000) := by
  have h := checkLog_sound (w := (178886625933 / 678886625933)) (n := 12)
    (lo := (53973169 / 100000000)) (hi := (539731691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((428886625933 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(428886625933 / 250000000000) = 1/(250000000000 / 428886625933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8753 : Bounds (53973169 / 100000000) (539731691 / 1000000000) (Real.log (428886625933 / 250000000000)) := by
  have h := reflection_log_8753_neg
  have he : Real.log (428886625933 / 250000000000) = -Real.log (250000000000 / 428886625933) := by
    rw [show ((428886625933 / 250000000000) : ℝ) = ((250000000000 / 428886625933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8754_neg : (108161291 / 200000000) ≤ -Real.log (250000000000 / 429347826087) ∧
    -Real.log (250000000000 / 429347826087) ≤ (67600807 / 125000000) := by
  have h := checkLog_sound (w := (179347826087 / 679347826087)) (n := 12)
    (lo := (108161291 / 200000000)) (hi := (67600807 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429347826087 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(429347826087 / 250000000000) = 1/(250000000000 / 429347826087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8754 : Bounds (108161291 / 200000000) (67600807 / 125000000) (Real.log (429347826087 / 250000000000)) := by
  have h := reflection_log_8754_neg
  have he : Real.log (429347826087 / 250000000000) = -Real.log (250000000000 / 429347826087) := by
    rw [show ((429347826087 / 250000000000) : ℝ) = ((250000000000 / 429347826087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8755_neg : (234676787 / 1000000000) ≤ -Real.log (2000 / 2529) ∧
    -Real.log (2000 / 2529) ≤ (58669197 / 250000000) := by
  have h := checkLog_sound (w := (529 / 4529)) (n := 12)
    (lo := (234676787 / 1000000000)) (hi := (58669197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2529 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2529 / 2000) = 1/(2000 / 2529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8755 : Bounds (234676787 / 1000000000) (58669197 / 250000000) (Real.log (2529 / 2000)) := by
  have h := reflection_log_8755_neg
  have he : Real.log (2529 / 2000) = -Real.log (2000 / 2529) := by
    rw [show ((2529 / 2000) : ℝ) = ((2000 / 2529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8756_neg : (153602369 / 500000000) ≤ -Real.log (1471 / 2000) ∧
    -Real.log (1471 / 2000) ≤ (307204739 / 1000000000) := by
  have h := checkLog_sound (w := (529 / 3471)) (n := 12)
    (lo := (153602369 / 500000000)) (hi := (307204739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1471) = 1/(1471 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8756 : Bounds (-307204739 / 1000000000) (-153602369 / 500000000) (Real.log (1471 / 2000)) := by
  have h := reflection_log_8756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8757_neg : (52893 / 200000000) ≤ -Real.log (2000000 / 2000529) ∧
    -Real.log (2000000 / 2000529) ≤ (132233 / 500000000) := by
  have h := checkLog_sound (w := (529 / 4000529)) (n := 12)
    (lo := (52893 / 200000000)) (hi := (132233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000529 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000529 / 2000000) = 1/(2000000 / 2000529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8757 : Bounds (52893 / 200000000) (132233 / 500000000) (Real.log (2000529 / 2000000)) := by
  have h := reflection_log_8757_neg
  have he : Real.log (2000529 / 2000000) = -Real.log (2000000 / 2000529) := by
    rw [show ((2000529 / 2000000) : ℝ) = ((2000000 / 2000529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8758_neg : (132267 / 500000000) ≤ -Real.log (1999471 / 2000000) ∧
    -Real.log (1999471 / 2000000) ≤ (52907 / 200000000) := by
  have h := checkLog_sound (w := (529 / 3999471)) (n := 12)
    (lo := (132267 / 500000000)) (hi := (52907 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999471) = 1/(1999471 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8758 : Bounds (-52907 / 200000000) (-132267 / 500000000) (Real.log (1999471 / 2000000)) := by
  have h := reflection_log_8758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8759_neg : (125365769 / 1000000000) ≤ -Real.log (1000000 / 1133563) ∧
    -Real.log (1000000 / 1133563) ≤ (12536577 / 100000000) := by
  have h := checkLog_sound (w := (133563 / 2133563)) (n := 12)
    (lo := (125365769 / 1000000000)) (hi := (12536577 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1133563 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1133563 / 1000000) = 1/(1000000 / 1133563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8759 : Bounds (125365769 / 1000000000) (12536577 / 100000000) (Real.log (1133563 / 1000000)) := by
  have h := reflection_log_8759_neg
  have he : Real.log (1133563 / 1000000) = -Real.log (1000000 / 1133563) := by
    rw [show ((1133563 / 1000000) : ℝ) = ((1000000 / 1133563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8760_neg : (71682939 / 500000000) ≤ -Real.log (866437 / 1000000) ∧
    -Real.log (866437 / 1000000) ≤ (143365879 / 1000000000) := by
  have h := checkLog_sound (w := (133563 / 1866437)) (n := 12)
    (lo := (71682939 / 500000000)) (hi := (143365879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 866437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 866437) = 1/(866437 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8760 : Bounds (-143365879 / 1000000000) (-71682939 / 500000000) (Real.log (866437 / 1000000)) := by
  have h := reflection_log_8760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8761_neg : (62913079 / 500000000) ≤ -Real.log (200000 / 226817) ∧
    -Real.log (200000 / 226817) ≤ (125826159 / 1000000000) := by
  have h := checkLog_sound (w := (26817 / 426817)) (n := 12)
    (lo := (62913079 / 500000000)) (hi := (125826159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226817 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226817 / 200000) = 1/(200000 / 226817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8761 : Bounds (62913079 / 500000000) (125826159 / 1000000000) (Real.log (226817 / 200000)) := by
  have h := reflection_log_8761_neg
  have he : Real.log (226817 / 200000) = -Real.log (200000 / 226817) := by
    rw [show ((226817 / 200000) : ℝ) = ((200000 / 226817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8762_neg : (143968527 / 1000000000) ≤ -Real.log (173183 / 200000) ∧
    -Real.log (173183 / 200000) ≤ (8998033 / 62500000) := by
  have h := checkLog_sound (w := (26817 / 373183)) (n := 12)
    (lo := (143968527 / 1000000000)) (hi := (8998033 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173183) = 1/(173183 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8762 : Bounds (-8998033 / 62500000) (-143968527 / 1000000000) (Real.log (173183 / 200000)) := by
  have h := reflection_log_8762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8763_neg : (18142369 / 1000000000) ≤ -Real.log (39280848511 / 40000000000) ∧
    -Real.log (39280848511 / 40000000000) ≤ (1814237 / 100000000) := by
  have h := checkLog_sound (w := (719151489 / 79280848511)) (n := 12)
    (lo := (18142369 / 1000000000)) (hi := (1814237 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39280848511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39280848511) = 1/(39280848511 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8763 : Bounds (-1814237 / 100000000) (-18142369 / 1000000000) (Real.log (39280848511 / 40000000000)) := by
  have h := reflection_log_8763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8764_neg : (18000109 / 1000000000) ≤ -Real.log (982160925031 / 1000000000000) ∧
    -Real.log (982160925031 / 1000000000000) ≤ (1800011 / 100000000) := by
  have h := checkLog_sound (w := (17839074969 / 1982160925031)) (n := 12)
    (lo := (18000109 / 1000000000)) (hi := (1800011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982160925031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982160925031) = 1/(982160925031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8764 : Bounds (-1800011 / 100000000) (-18000109 / 1000000000) (Real.log (982160925031 / 1000000000000)) := by
  have h := reflection_log_8764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8765_neg : (1049733 / 3906250) ≤ -Real.log (500000000000 / 654152004127) ∧
    -Real.log (500000000000 / 654152004127) ≤ (268731649 / 1000000000) := by
  have h := checkLog_sound (w := (154152004127 / 1154152004127)) (n := 12)
    (lo := (1049733 / 3906250)) (hi := (268731649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((654152004127 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(654152004127 / 500000000000) = 1/(500000000000 / 654152004127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8765 : Bounds (1049733 / 3906250) (268731649 / 1000000000) (Real.log (654152004127 / 500000000000)) := by
  have h := reflection_log_8765_neg
  have he : Real.log (654152004127 / 500000000000) = -Real.log (500000000000 / 654152004127) := by
    rw [show ((654152004127 / 500000000000) : ℝ) = ((500000000000 / 654152004127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8766_neg : (134897343 / 500000000) ≤ -Real.log (250000000000 / 327423881097) ∧
    -Real.log (250000000000 / 327423881097) ≤ (269794687 / 1000000000) := by
  have h := checkLog_sound (w := (77423881097 / 577423881097)) (n := 12)
    (lo := (134897343 / 500000000)) (hi := (269794687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327423881097 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327423881097 / 250000000000) = 1/(250000000000 / 327423881097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8766 : Bounds (134897343 / 500000000) (269794687 / 1000000000) (Real.log (327423881097 / 250000000000)) := by
  have h := reflection_log_8766_neg
  have he : Real.log (327423881097 / 250000000000) = -Real.log (250000000000 / 327423881097) := by
    rw [show ((327423881097 / 250000000000) : ℝ) = ((250000000000 / 327423881097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8767_neg : (108161291 / 200000000) ≤ -Real.log (500000000000 / 858695652173) ∧
    -Real.log (500000000000 / 858695652173) ≤ (67600807 / 125000000) := by
  have h := checkLog_sound (w := (358695652173 / 1358695652173)) (n := 12)
    (lo := (108161291 / 200000000)) (hi := (67600807 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858695652173 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(858695652173 / 500000000000) = 1/(500000000000 / 858695652173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8767 : Bounds (108161291 / 200000000) (67600807 / 125000000) (Real.log (858695652173 / 500000000000)) := by
  have h := reflection_log_8767_neg
  have he : Real.log (858695652173 / 500000000000) = -Real.log (500000000000 / 858695652173) := by
    rw [show ((858695652173 / 500000000000) : ℝ) = ((500000000000 / 858695652173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
