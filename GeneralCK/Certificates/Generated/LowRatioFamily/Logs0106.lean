import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6784_neg : (200498979 / 1000000000) ≤ -Real.log (500000000000 / 611006182749) ∧
    -Real.log (500000000000 / 611006182749) ≤ (10024949 / 50000000) := by
  have h := checkLog_sound (w := (111006182749 / 1111006182749)) (n := 12)
    (lo := (200498979 / 1000000000)) (hi := (10024949 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611006182749 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611006182749 / 500000000000) = 1/(500000000000 / 611006182749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6784 : Bounds (200498979 / 1000000000) (10024949 / 50000000) (Real.log (611006182749 / 500000000000)) := by
  have h := reflection_log_6784_neg
  have he : Real.log (611006182749 / 500000000000) = -Real.log (500000000000 / 611006182749) := by
    rw [show ((611006182749 / 500000000000) : ℝ) = ((500000000000 / 611006182749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6785_neg : (100502017 / 500000000) ≤ -Real.log (62500000000 / 76414356521) ∧
    -Real.log (62500000000 / 76414356521) ≤ (40200807 / 200000000) := by
  have h := checkLog_sound (w := (13914356521 / 138914356521)) (n := 12)
    (lo := (100502017 / 500000000)) (hi := (40200807 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76414356521 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76414356521 / 62500000000) = 1/(62500000000 / 76414356521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6785 : Bounds (100502017 / 500000000) (40200807 / 200000000) (Real.log (76414356521 / 62500000000)) := by
  have h := reflection_log_6785_neg
  have he : Real.log (76414356521 / 62500000000) = -Real.log (62500000000 / 76414356521) := by
    rw [show ((76414356521 / 62500000000) : ℝ) = ((62500000000 / 76414356521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6786_neg : (402549289 / 1000000000) ≤ -Real.log (500000000000 / 747816321437) ∧
    -Real.log (500000000000 / 747816321437) ≤ (40254929 / 100000000) := by
  have h := checkLog_sound (w := (247816321437 / 1247816321437)) (n := 12)
    (lo := (402549289 / 1000000000)) (hi := (40254929 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747816321437 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747816321437 / 500000000000) = 1/(500000000000 / 747816321437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6786 : Bounds (402549289 / 1000000000) (40254929 / 100000000) (Real.log (747816321437 / 500000000000)) := by
  have h := reflection_log_6786_neg
  have he : Real.log (747816321437 / 500000000000) = -Real.log (500000000000 / 747816321437) := by
    rw [show ((747816321437 / 500000000000) : ℝ) = ((500000000000 / 747816321437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6787_neg : (201378753 / 500000000) ≤ -Real.log (500000000000 / 747972045427) ∧
    -Real.log (500000000000 / 747972045427) ≤ (402757507 / 1000000000) := by
  have h := checkLog_sound (w := (247972045427 / 1247972045427)) (n := 12)
    (lo := (201378753 / 500000000)) (hi := (402757507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747972045427 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747972045427 / 500000000000) = 1/(500000000000 / 747972045427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6787 : Bounds (201378753 / 500000000) (402757507 / 1000000000) (Real.log (747972045427 / 500000000000)) := by
  have h := reflection_log_6787_neg
  have he : Real.log (747972045427 / 500000000000) = -Real.log (500000000000 / 747972045427) := by
    rw [show ((747972045427 / 500000000000) : ℝ) = ((500000000000 / 747972045427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6788_neg : (5666283 / 31250000) ≤ -Real.log (2500 / 2997) ∧
    -Real.log (2500 / 2997) ≤ (181321057 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 5497)) (n := 12)
    (lo := (5666283 / 31250000)) (hi := (181321057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2997 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2997 / 2500) = 1/(2500 / 2997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6788 : Bounds (5666283 / 31250000) (181321057 / 1000000000) (Real.log (2997 / 2500)) := by
  have h := reflection_log_6788_neg
  have he : Real.log (2997 / 2500) = -Real.log (2500 / 2997) := by
    rw [show ((2997 / 2500) : ℝ) = ((2500 / 2997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6789_neg : (8865787 / 40000000) ≤ -Real.log (2003 / 2500) ∧
    -Real.log (2003 / 2500) ≤ (55411169 / 250000000) := by
  have h := checkLog_sound (w := (497 / 4503)) (n := 12)
    (lo := (8865787 / 40000000)) (hi := (55411169 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2003) = 1/(2003 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6789 : Bounds (-55411169 / 250000000) (-8865787 / 40000000) (Real.log (2003 / 2500)) := by
  have h := reflection_log_6789_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6790_neg : (9939 / 50000000) ≤ -Real.log (2500000 / 2500497) ∧
    -Real.log (2500000 / 2500497) ≤ (198781 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 5000497)) (n := 12)
    (lo := (9939 / 50000000)) (hi := (198781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500497 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500497 / 2500000) = 1/(2500000 / 2500497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6790 : Bounds (9939 / 50000000) (198781 / 1000000000) (Real.log (2500497 / 2500000)) := by
  have h := reflection_log_6790_neg
  have he : Real.log (2500497 / 2500000) = -Real.log (2500000 / 2500497) := by
    rw [show ((2500497 / 2500000) : ℝ) = ((2500000 / 2500497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6791_neg : (198819 / 1000000000) ≤ -Real.log (2499503 / 2500000) ∧
    -Real.log (2499503 / 2500000) ≤ (9941 / 50000000) := by
  have h := checkLog_sound (w := (497 / 4999503)) (n := 12)
    (lo := (198819 / 1000000000)) (hi := (9941 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499503) = 1/(2499503 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6791 : Bounds (-9941 / 50000000) (-198819 / 1000000000) (Real.log (2499503 / 2500000)) := by
  have h := reflection_log_6791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6792_neg : (95280179 / 1000000000) ≤ -Real.log (1000000 / 1099967) ∧
    -Real.log (1000000 / 1099967) ≤ (4764009 / 50000000) := by
  have h := checkLog_sound (w := (99967 / 2099967)) (n := 12)
    (lo := (95280179 / 1000000000)) (hi := (4764009 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099967 / 1000000) = 1/(1000000 / 1099967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6792 : Bounds (95280179 / 1000000000) (4764009 / 50000000) (Real.log (1099967 / 1000000)) := by
  have h := reflection_log_6792_neg
  have he : Real.log (1099967 / 1000000) = -Real.log (1000000 / 1099967) := by
    rw [show ((1099967 / 1000000) : ℝ) = ((1000000 / 1099967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6793_neg : (105323849 / 1000000000) ≤ -Real.log (900033 / 1000000) ∧
    -Real.log (900033 / 1000000) ≤ (2106477 / 20000000) := by
  have h := checkLog_sound (w := (99967 / 1900033)) (n := 12)
    (lo := (105323849 / 1000000000)) (hi := (2106477 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900033) = 1/(900033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6793 : Bounds (-2106477 / 20000000) (-105323849 / 1000000000) (Real.log (900033 / 1000000)) := by
  have h := reflection_log_6793_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6794_neg : (23876631 / 250000000) ≤ -Real.log (125000 / 137527) ∧
    -Real.log (125000 / 137527) ≤ (3820261 / 40000000) := by
  have h := checkLog_sound (w := (12527 / 262527)) (n := 12)
    (lo := (23876631 / 250000000)) (hi := (3820261 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137527 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137527 / 125000) = 1/(125000 / 137527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6794 : Bounds (23876631 / 250000000) (3820261 / 40000000) (Real.log (137527 / 125000)) := by
  have h := reflection_log_6794_neg
  have he : Real.log (137527 / 125000) = -Real.log (125000 / 137527) := by
    rw [show ((137527 / 125000) : ℝ) = ((125000 / 137527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6795_neg : (3300017 / 31250000) ≤ -Real.log (112473 / 125000) ∧
    -Real.log (112473 / 125000) ≤ (21120109 / 200000000) := by
  have h := checkLog_sound (w := (12527 / 237473)) (n := 12)
    (lo := (3300017 / 31250000)) (hi := (21120109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112473) = 1/(112473 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6795 : Bounds (-21120109 / 200000000) (-3300017 / 31250000) (Real.log (112473 / 125000)) := by
  have h := reflection_log_6795_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6796_neg : (504701 / 50000000) ≤ -Real.log (15468074271 / 15625000000) ∧
    -Real.log (15468074271 / 15625000000) ≤ (10094021 / 1000000000) := by
  have h := checkLog_sound (w := (156925729 / 31093074271)) (n := 12)
    (lo := (504701 / 50000000)) (hi := (10094021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15468074271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15468074271) = 1/(15468074271 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6796 : Bounds (-10094021 / 1000000000) (-504701 / 50000000) (Real.log (15468074271 / 15625000000)) := by
  have h := reflection_log_6796_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6797_neg : (1004367 / 100000000) ≤ -Real.log (990006598911 / 1000000000000) ∧
    -Real.log (990006598911 / 1000000000000) ≤ (10043671 / 1000000000) := by
  have h := checkLog_sound (w := (9993401089 / 1990006598911)) (n := 12)
    (lo := (1004367 / 100000000)) (hi := (10043671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990006598911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990006598911) = 1/(990006598911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6797 : Bounds (-10043671 / 1000000000) (-1004367 / 100000000) (Real.log (990006598911 / 1000000000000)) := by
  have h := reflection_log_6797_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6798_neg : (200604029 / 1000000000) ≤ -Real.log (62500000000 / 76383796483) ∧
    -Real.log (62500000000 / 76383796483) ≤ (20060403 / 100000000) := by
  have h := checkLog_sound (w := (13883796483 / 138883796483)) (n := 12)
    (lo := (200604029 / 1000000000)) (hi := (20060403 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76383796483 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76383796483 / 62500000000) = 1/(62500000000 / 76383796483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6798 : Bounds (200604029 / 1000000000) (20060403 / 100000000) (Real.log (76383796483 / 62500000000)) := by
  have h := reflection_log_6798_neg
  have he : Real.log (76383796483 / 62500000000) = -Real.log (62500000000 / 76383796483) := by
    rw [show ((76383796483 / 62500000000) : ℝ) = ((62500000000 / 76383796483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6799_neg : (50276767 / 250000000) ≤ -Real.log (250000000000 / 305688920897) ∧
    -Real.log (250000000000 / 305688920897) ≤ (201107069 / 1000000000) := by
  have h := checkLog_sound (w := (55688920897 / 555688920897)) (n := 12)
    (lo := (50276767 / 250000000)) (hi := (201107069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305688920897 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305688920897 / 250000000000) = 1/(250000000000 / 305688920897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6799 : Bounds (50276767 / 250000000) (201107069 / 1000000000) (Real.log (305688920897 / 250000000000)) := by
  have h := reflection_log_6799_neg
  have he : Real.log (305688920897 / 250000000000) = -Real.log (250000000000 / 305688920897) := by
    rw [show ((305688920897 / 250000000000) : ℝ) = ((250000000000 / 305688920897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6800_neg : (201378753 / 500000000) ≤ -Real.log (250000000000 / 373986022713) ∧
    -Real.log (250000000000 / 373986022713) ≤ (402757507 / 1000000000) := by
  have h := checkLog_sound (w := (123986022713 / 623986022713)) (n := 12)
    (lo := (201378753 / 500000000)) (hi := (402757507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373986022713 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373986022713 / 250000000000) = 1/(250000000000 / 373986022713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6800 : Bounds (201378753 / 500000000) (402757507 / 1000000000) (Real.log (373986022713 / 250000000000)) := by
  have h := reflection_log_6800_neg
  have he : Real.log (373986022713 / 250000000000) = -Real.log (250000000000 / 373986022713) := by
    rw [show ((373986022713 / 250000000000) : ℝ) = ((250000000000 / 373986022713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6801_neg : (402965731 / 1000000000) ≤ -Real.log (15625000000 / 23378994009) ∧
    -Real.log (15625000000 / 23378994009) ≤ (100741433 / 250000000) := by
  have h := checkLog_sound (w := (7753994009 / 39003994009)) (n := 12)
    (lo := (402965731 / 1000000000)) (hi := (100741433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23378994009 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23378994009 / 15625000000) = 1/(15625000000 / 23378994009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6801 : Bounds (402965731 / 1000000000) (100741433 / 250000000) (Real.log (23378994009 / 15625000000)) := by
  have h := reflection_log_6801_neg
  have he : Real.log (23378994009 / 15625000000) = -Real.log (15625000000 / 23378994009) := by
    rw [show ((23378994009 / 15625000000) : ℝ) = ((15625000000 / 23378994009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6802_neg : (181404469 / 1000000000) ≤ -Real.log (10000 / 11989) ∧
    -Real.log (10000 / 11989) ≤ (18140447 / 100000000) := by
  have h := checkLog_sound (w := (1989 / 21989)) (n := 12)
    (lo := (181404469 / 1000000000)) (hi := (18140447 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11989 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11989 / 10000) = 1/(10000 / 11989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6802 : Bounds (181404469 / 1000000000) (18140447 / 100000000) (Real.log (11989 / 10000)) := by
  have h := reflection_log_6802_neg
  have he : Real.log (11989 / 10000) = -Real.log (10000 / 11989) := by
    rw [show ((11989 / 10000) : ℝ) = ((10000 / 11989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6803_neg : (44353899 / 200000000) ≤ -Real.log (8011 / 10000) ∧
    -Real.log (8011 / 10000) ≤ (27721187 / 125000000) := by
  have h := checkLog_sound (w := (1989 / 18011)) (n := 12)
    (lo := (44353899 / 200000000)) (hi := (27721187 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8011) = 1/(8011 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6803 : Bounds (-27721187 / 125000000) (-44353899 / 200000000) (Real.log (8011 / 10000)) := by
  have h := reflection_log_6803_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6804_neg : (1243 / 6250000) ≤ -Real.log (10000000 / 10001989) ∧
    -Real.log (10000000 / 10001989) ≤ (198881 / 1000000000) := by
  have h := checkLog_sound (w := (1989 / 20001989)) (n := 12)
    (lo := (1243 / 6250000)) (hi := (198881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001989 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001989 / 10000000) = 1/(10000000 / 10001989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6804 : Bounds (1243 / 6250000) (198881 / 1000000000) (Real.log (10001989 / 10000000)) := by
  have h := reflection_log_6804_neg
  have he : Real.log (10001989 / 10000000) = -Real.log (10000000 / 10001989) := by
    rw [show ((10001989 / 10000000) : ℝ) = ((10000000 / 10001989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6805_neg : (198919 / 1000000000) ≤ -Real.log (9998011 / 10000000) ∧
    -Real.log (9998011 / 10000000) ≤ (4973 / 25000000) := by
  have h := checkLog_sound (w := (1989 / 19998011)) (n := 12)
    (lo := (198919 / 1000000000)) (hi := (4973 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998011) = 1/(9998011 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6805 : Bounds (-4973 / 25000000) (-198919 / 1000000000) (Real.log (9998011 / 10000000)) := by
  have h := reflection_log_6805_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6806_neg : (95326543 / 1000000000) ≤ -Real.log (500000 / 550009) ∧
    -Real.log (500000 / 550009) ≤ (5957909 / 62500000) := by
  have h := checkLog_sound (w := (50009 / 1050009)) (n := 12)
    (lo := (95326543 / 1000000000)) (hi := (5957909 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550009 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(550009 / 500000) = 1/(500000 / 550009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6806 : Bounds (95326543 / 1000000000) (5957909 / 62500000) (Real.log (550009 / 500000)) := by
  have h := reflection_log_6806_neg
  have he : Real.log (550009 / 500000) = -Real.log (500000 / 550009) := by
    rw [show ((550009 / 500000) : ℝ) = ((500000 / 550009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6807_neg : (21076103 / 200000000) ≤ -Real.log (449991 / 500000) ∧
    -Real.log (449991 / 500000) ≤ (26345129 / 250000000) := by
  have h := checkLog_sound (w := (50009 / 949991)) (n := 12)
    (lo := (21076103 / 200000000)) (hi := (26345129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 449991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 449991) = 1/(449991 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6807 : Bounds (-26345129 / 250000000) (-21076103 / 200000000) (Real.log (449991 / 500000)) := by
  have h := reflection_log_6807_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6808_neg : (95552877 / 1000000000) ≤ -Real.log (1000000 / 1100267) ∧
    -Real.log (1000000 / 1100267) ≤ (47776439 / 500000000) := by
  have h := checkLog_sound (w := (100267 / 2100267)) (n := 12)
    (lo := (95552877 / 1000000000)) (hi := (47776439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100267 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100267 / 1000000) = 1/(1000000 / 1100267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6808 : Bounds (95552877 / 1000000000) (47776439 / 500000000) (Real.log (1100267 / 1000000)) := by
  have h := reflection_log_6808_neg
  have he : Real.log (1100267 / 1000000) = -Real.log (1000000 / 1100267) := by
    rw [show ((1100267 / 1000000) : ℝ) = ((1000000 / 1100267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6809_neg : (52828613 / 500000000) ≤ -Real.log (899733 / 1000000) ∧
    -Real.log (899733 / 1000000) ≤ (105657227 / 1000000000) := by
  have h := checkLog_sound (w := (100267 / 1899733)) (n := 12)
    (lo := (52828613 / 500000000)) (hi := (105657227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899733) = 1/(899733 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6809 : Bounds (-105657227 / 1000000000) (-52828613 / 500000000) (Real.log (899733 / 1000000)) := by
  have h := reflection_log_6809_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6810_neg : (2526087 / 250000000) ≤ -Real.log (989946528711 / 1000000000000) ∧
    -Real.log (989946528711 / 1000000000000) ≤ (10104349 / 1000000000) := by
  have h := checkLog_sound (w := (10053471289 / 1989946528711)) (n := 12)
    (lo := (2526087 / 250000000)) (hi := (10104349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989946528711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989946528711) = 1/(989946528711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6810 : Bounds (-10104349 / 1000000000) (-2526087 / 250000000) (Real.log (989946528711 / 1000000000000)) := by
  have h := reflection_log_6810_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6811_neg : (2513493 / 250000000) ≤ -Real.log (247499099919 / 250000000000) ∧
    -Real.log (247499099919 / 250000000000) ≤ (10053973 / 1000000000) := by
  have h := checkLog_sound (w := (2500900081 / 497499099919)) (n := 12)
    (lo := (2513493 / 250000000)) (hi := (10053973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247499099919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247499099919) = 1/(247499099919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6811 : Bounds (-10053973 / 1000000000) (-2513493 / 250000000) (Real.log (247499099919 / 250000000000)) := by
  have h := reflection_log_6811_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6812_neg : (200707059 / 1000000000) ≤ -Real.log (500000000000 / 611133333777) ∧
    -Real.log (500000000000 / 611133333777) ≤ (10035353 / 50000000) := by
  have h := checkLog_sound (w := (111133333777 / 1111133333777)) (n := 12)
    (lo := (200707059 / 1000000000)) (hi := (10035353 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611133333777 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611133333777 / 500000000000) = 1/(500000000000 / 611133333777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6812 : Bounds (200707059 / 1000000000) (10035353 / 50000000) (Real.log (611133333777 / 500000000000)) := by
  have h := reflection_log_6812_neg
  have he : Real.log (611133333777 / 500000000000) = -Real.log (500000000000 / 611133333777) := by
    rw [show ((611133333777 / 500000000000) : ℝ) = ((500000000000 / 611133333777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6813_neg : (201210103 / 1000000000) ≤ -Real.log (3125000000 / 3821505241) ∧
    -Real.log (3125000000 / 3821505241) ≤ (25151263 / 125000000) := by
  have h := checkLog_sound (w := (696505241 / 6946505241)) (n := 12)
    (lo := (201210103 / 1000000000)) (hi := (25151263 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3821505241 / 3125000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3821505241 / 3125000000) = 1/(3125000000 / 3821505241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6813 : Bounds (201210103 / 1000000000) (25151263 / 125000000) (Real.log (3821505241 / 3125000000)) := by
  have h := reflection_log_6813_neg
  have he : Real.log (3821505241 / 3125000000) = -Real.log (3125000000 / 3821505241) := by
    rw [show ((3821505241 / 3125000000) : ℝ) = ((3125000000 / 3821505241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6814_neg : (402965731 / 1000000000) ≤ -Real.log (500000000000 / 748127808287) ∧
    -Real.log (500000000000 / 748127808287) ≤ (100741433 / 250000000) := by
  have h := checkLog_sound (w := (248127808287 / 1248127808287)) (n := 12)
    (lo := (402965731 / 1000000000)) (hi := (100741433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748127808287 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748127808287 / 500000000000) = 1/(500000000000 / 748127808287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6814 : Bounds (402965731 / 1000000000) (100741433 / 250000000) (Real.log (748127808287 / 500000000000)) := by
  have h := reflection_log_6814_neg
  have he : Real.log (748127808287 / 500000000000) = -Real.log (500000000000 / 748127808287) := by
    rw [show ((748127808287 / 500000000000) : ℝ) = ((500000000000 / 748127808287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6815_neg : (80634793 / 200000000) ≤ -Real.log (500000000000 / 748283610037) ∧
    -Real.log (500000000000 / 748283610037) ≤ (201586983 / 500000000) := by
  have h := checkLog_sound (w := (248283610037 / 1248283610037)) (n := 12)
    (lo := (80634793 / 200000000)) (hi := (201586983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748283610037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748283610037 / 500000000000) = 1/(500000000000 / 748283610037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6815 : Bounds (80634793 / 200000000) (201586983 / 500000000) (Real.log (748283610037 / 500000000000)) := by
  have h := reflection_log_6815_neg
  have he : Real.log (748283610037 / 500000000000) = -Real.log (500000000000 / 748283610037) := by
    rw [show ((748283610037 / 500000000000) : ℝ) = ((500000000000 / 748283610037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6816_neg : (45371969 / 250000000) ≤ -Real.log (1000 / 1199) ∧
    -Real.log (1000 / 1199) ≤ (181487877 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 2199)) (n := 12)
    (lo := (45371969 / 250000000)) (hi := (181487877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199 / 1000) = 1/(1000 / 1199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6816 : Bounds (45371969 / 250000000) (181487877 / 1000000000) (Real.log (1199 / 1000)) := by
  have h := reflection_log_6816_neg
  have he : Real.log (1199 / 1000) = -Real.log (1000 / 1199) := by
    rw [show ((1199 / 1000) : ℝ) = ((1000 / 1199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6817_neg : (221894331 / 1000000000) ≤ -Real.log (801 / 1000) ∧
    -Real.log (801 / 1000) ≤ (55473583 / 250000000) := by
  have h := checkLog_sound (w := (199 / 1801)) (n := 12)
    (lo := (221894331 / 1000000000)) (hi := (55473583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 801) = 1/(801 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6817 : Bounds (-55473583 / 250000000) (-221894331 / 1000000000) (Real.log (801 / 1000)) := by
  have h := reflection_log_6817_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6818_neg : (9949 / 50000000) ≤ -Real.log (1000000 / 1000199) ∧
    -Real.log (1000000 / 1000199) ≤ (198981 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 2000199)) (n := 12)
    (lo := (9949 / 50000000)) (hi := (198981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000199 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000199 / 1000000) = 1/(1000000 / 1000199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6818 : Bounds (9949 / 50000000) (198981 / 1000000000) (Real.log (1000199 / 1000000)) := by
  have h := reflection_log_6818_neg
  have he : Real.log (1000199 / 1000000) = -Real.log (1000000 / 1000199) := by
    rw [show ((1000199 / 1000000) : ℝ) = ((1000000 / 1000199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6819_neg : (199019 / 1000000000) ≤ -Real.log (999801 / 1000000) ∧
    -Real.log (999801 / 1000000) ≤ (9951 / 50000000) := by
  have h := checkLog_sound (w := (199 / 1999801)) (n := 12)
    (lo := (199019 / 1000000000)) (hi := (9951 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999801) = 1/(999801 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6819 : Bounds (-9951 / 50000000) (-199019 / 1000000000) (Real.log (999801 / 1000000)) := by
  have h := reflection_log_6819_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6820_neg : (19074581 / 200000000) ≤ -Real.log (1000000 / 1100069) ∧
    -Real.log (1000000 / 1100069) ≤ (47686453 / 500000000) := by
  have h := checkLog_sound (w := (100069 / 2100069)) (n := 12)
    (lo := (19074581 / 200000000)) (hi := (47686453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100069 / 1000000) = 1/(1000000 / 1100069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6820 : Bounds (19074581 / 200000000) (47686453 / 500000000) (Real.log (1100069 / 1000000)) := by
  have h := reflection_log_6820_neg
  have he : Real.log (1100069 / 1000000) = -Real.log (1000000 / 1100069) := by
    rw [show ((1100069 / 1000000) : ℝ) = ((1000000 / 1100069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6821_neg : (21087437 / 200000000) ≤ -Real.log (899931 / 1000000) ∧
    -Real.log (899931 / 1000000) ≤ (52718593 / 500000000) := by
  have h := checkLog_sound (w := (100069 / 1899931)) (n := 12)
    (lo := (21087437 / 200000000)) (hi := (52718593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899931) = 1/(899931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6821 : Bounds (-52718593 / 500000000) (-21087437 / 200000000) (Real.log (899931 / 1000000)) := by
  have h := reflection_log_6821_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6822_neg : (23899807 / 250000000) ≤ -Real.log (500000 / 550159) ∧
    -Real.log (500000 / 550159) ≤ (95599229 / 1000000000) := by
  have h := checkLog_sound (w := (50159 / 1050159)) (n := 12)
    (lo := (23899807 / 250000000)) (hi := (95599229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550159 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(550159 / 500000) = 1/(500000 / 550159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6822 : Bounds (23899807 / 250000000) (95599229 / 1000000000) (Real.log (550159 / 500000)) := by
  have h := reflection_log_6822_neg
  have he : Real.log (550159 / 500000) = -Real.log (500000 / 550159) := by
    rw [show ((550159 / 500000) : ℝ) = ((500000 / 550159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6823_neg : (105713911 / 1000000000) ≤ -Real.log (449841 / 500000) ∧
    -Real.log (449841 / 500000) ≤ (13214239 / 125000000) := by
  have h := checkLog_sound (w := (50159 / 949841)) (n := 12)
    (lo := (105713911 / 1000000000)) (hi := (13214239 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 449841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 449841) = 1/(449841 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6823 : Bounds (-13214239 / 125000000) (-105713911 / 1000000000) (Real.log (449841 / 500000)) := by
  have h := reflection_log_6823_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6824_neg : (5057341 / 500000000) ≤ -Real.log (247484074719 / 250000000000) ∧
    -Real.log (247484074719 / 250000000000) ≤ (10114683 / 1000000000) := by
  have h := checkLog_sound (w := (2515925281 / 497484074719)) (n := 12)
    (lo := (5057341 / 500000000)) (hi := (10114683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247484074719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247484074719) = 1/(247484074719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6824 : Bounds (-10114683 / 1000000000) (-5057341 / 500000000) (Real.log (247484074719 / 250000000000)) := by
  have h := reflection_log_6824_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6825_neg : (251607 / 25000000) ≤ -Real.log (989986195239 / 1000000000000) ∧
    -Real.log (989986195239 / 1000000000000) ≤ (10064281 / 1000000000) := by
  have h := checkLog_sound (w := (10013804761 / 1989986195239)) (n := 12)
    (lo := (251607 / 25000000)) (hi := (10064281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989986195239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989986195239) = 1/(989986195239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6825 : Bounds (-10064281 / 1000000000) (-251607 / 25000000) (Real.log (989986195239 / 1000000000000)) := by
  have h := reflection_log_6825_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6826_neg : (20081009 / 100000000) ≤ -Real.log (500000000000 / 611196302827) ∧
    -Real.log (500000000000 / 611196302827) ≤ (200810091 / 1000000000) := by
  have h := checkLog_sound (w := (111196302827 / 1111196302827)) (n := 12)
    (lo := (20081009 / 100000000)) (hi := (200810091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611196302827 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611196302827 / 500000000000) = 1/(500000000000 / 611196302827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6826 : Bounds (20081009 / 100000000) (200810091 / 1000000000) (Real.log (611196302827 / 500000000000)) := by
  have h := reflection_log_6826_neg
  have he : Real.log (611196302827 / 500000000000) = -Real.log (500000000000 / 611196302827) := by
    rw [show ((611196302827 / 500000000000) : ℝ) = ((500000000000 / 611196302827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6827_neg : (10065657 / 50000000) ≤ -Real.log (500000000000 / 611503842469) ∧
    -Real.log (500000000000 / 611503842469) ≤ (201313141 / 1000000000) := by
  have h := checkLog_sound (w := (111503842469 / 1111503842469)) (n := 12)
    (lo := (10065657 / 50000000)) (hi := (201313141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611503842469 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611503842469 / 500000000000) = 1/(500000000000 / 611503842469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6827 : Bounds (10065657 / 50000000) (201313141 / 1000000000) (Real.log (611503842469 / 500000000000)) := by
  have h := reflection_log_6827_neg
  have he : Real.log (611503842469 / 500000000000) = -Real.log (500000000000 / 611503842469) := by
    rw [show ((611503842469 / 500000000000) : ℝ) = ((500000000000 / 611503842469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6828_neg : (80634793 / 200000000) ≤ -Real.log (125000000000 / 187070902509) ∧
    -Real.log (125000000000 / 187070902509) ≤ (201586983 / 500000000) := by
  have h := checkLog_sound (w := (62070902509 / 312070902509)) (n := 12)
    (lo := (80634793 / 200000000)) (hi := (201586983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187070902509 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187070902509 / 125000000000) = 1/(125000000000 / 187070902509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6828 : Bounds (80634793 / 200000000) (201586983 / 500000000) (Real.log (187070902509 / 125000000000)) := by
  have h := reflection_log_6828_neg
  have he : Real.log (187070902509 / 125000000000) = -Real.log (125000000000 / 187070902509) := by
    rw [show ((187070902509 / 125000000000) : ℝ) = ((125000000000 / 187070902509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6829_neg : (403382207 / 1000000000) ≤ -Real.log (500000000000 / 748439450687) ∧
    -Real.log (500000000000 / 748439450687) ≤ (6302847 / 15625000) := by
  have h := checkLog_sound (w := (248439450687 / 1248439450687)) (n := 12)
    (lo := (403382207 / 1000000000)) (hi := (6302847 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748439450687 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748439450687 / 500000000000) = 1/(500000000000 / 748439450687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6829 : Bounds (403382207 / 1000000000) (6302847 / 15625000) (Real.log (748439450687 / 500000000000)) := by
  have h := reflection_log_6829_neg
  have he : Real.log (748439450687 / 500000000000) = -Real.log (500000000000 / 748439450687) := by
    rw [show ((748439450687 / 500000000000) : ℝ) = ((500000000000 / 748439450687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6830_neg : (7262851 / 40000000) ≤ -Real.log (10000 / 11991) ∧
    -Real.log (10000 / 11991) ≤ (45392819 / 250000000) := by
  have h := checkLog_sound (w := (1991 / 21991)) (n := 12)
    (lo := (7262851 / 40000000)) (hi := (45392819 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11991 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11991 / 10000) = 1/(10000 / 11991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6830 : Bounds (7262851 / 40000000) (45392819 / 250000000) (Real.log (11991 / 10000)) := by
  have h := reflection_log_6830_neg
  have he : Real.log (11991 / 10000) = -Real.log (10000 / 11991) := by
    rw [show ((11991 / 10000) : ℝ) = ((10000 / 11991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6831_neg : (222019183 / 1000000000) ≤ -Real.log (8009 / 10000) ∧
    -Real.log (8009 / 10000) ≤ (13876199 / 62500000) := by
  have h := checkLog_sound (w := (1991 / 18009)) (n := 12)
    (lo := (222019183 / 1000000000)) (hi := (13876199 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8009) = 1/(8009 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6831 : Bounds (-13876199 / 62500000) (-222019183 / 1000000000) (Real.log (8009 / 10000)) := by
  have h := reflection_log_6831_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6832_neg : (4977 / 25000000) ≤ -Real.log (10000000 / 10001991) ∧
    -Real.log (10000000 / 10001991) ≤ (199081 / 1000000000) := by
  have h := checkLog_sound (w := (1991 / 20001991)) (n := 12)
    (lo := (4977 / 25000000)) (hi := (199081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001991 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001991 / 10000000) = 1/(10000000 / 10001991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6832 : Bounds (4977 / 25000000) (199081 / 1000000000) (Real.log (10001991 / 10000000)) := by
  have h := reflection_log_6832_neg
  have he : Real.log (10001991 / 10000000) = -Real.log (10000000 / 10001991) := by
    rw [show ((10001991 / 10000000) : ℝ) = ((10000000 / 10001991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6833_neg : (199119 / 1000000000) ≤ -Real.log (9998009 / 10000000) ∧
    -Real.log (9998009 / 10000000) ≤ (2489 / 12500000) := by
  have h := checkLog_sound (w := (1991 / 19998009)) (n := 12)
    (lo := (199119 / 1000000000)) (hi := (2489 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998009) = 1/(9998009 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6833 : Bounds (-2489 / 12500000) (-199119 / 1000000000) (Real.log (9998009 / 10000000)) := by
  have h := reflection_log_6833_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6834_neg : (745463 / 7812500) ≤ -Real.log (25000 / 27503) ∧
    -Real.log (25000 / 27503) ≤ (19083853 / 200000000) := by
  have h := checkLog_sound (w := (2503 / 52503)) (n := 12)
    (lo := (745463 / 7812500)) (hi := (19083853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27503 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27503 / 25000) = 1/(25000 / 27503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6834 : Bounds (745463 / 7812500) (19083853 / 200000000) (Real.log (27503 / 25000)) := by
  have h := reflection_log_6834_neg
  have he : Real.log (27503 / 25000) = -Real.log (25000 / 27503) := by
    rw [show ((27503 / 25000) : ℝ) = ((25000 / 27503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6835_neg : (105493857 / 1000000000) ≤ -Real.log (22497 / 25000) ∧
    -Real.log (22497 / 25000) ≤ (52746929 / 500000000) := by
  have h := checkLog_sound (w := (2503 / 47497)) (n := 12)
    (lo := (105493857 / 1000000000)) (hi := (52746929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22497) = 1/(22497 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6835 : Bounds (-52746929 / 500000000) (-105493857 / 1000000000) (Real.log (22497 / 25000)) := by
  have h := reflection_log_6835_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6836_neg : (47822789 / 500000000) ≤ -Real.log (1000000 / 1100369) ∧
    -Real.log (1000000 / 1100369) ≤ (95645579 / 1000000000) := by
  have h := checkLog_sound (w := (100369 / 2100369)) (n := 12)
    (lo := (47822789 / 500000000)) (hi := (95645579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100369 / 1000000) = 1/(1000000 / 1100369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6836 : Bounds (47822789 / 500000000) (95645579 / 1000000000) (Real.log (1100369 / 1000000)) := by
  have h := reflection_log_6836_neg
  have he : Real.log (1100369 / 1000000) = -Real.log (1000000 / 1100369) := by
    rw [show ((1100369 / 1000000) : ℝ) = ((1000000 / 1100369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6837_neg : (105770599 / 1000000000) ≤ -Real.log (899631 / 1000000) ∧
    -Real.log (899631 / 1000000) ≤ (528853 / 5000000) := by
  have h := checkLog_sound (w := (100369 / 1899631)) (n := 12)
    (lo := (105770599 / 1000000000)) (hi := (528853 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899631) = 1/(899631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6837 : Bounds (-528853 / 5000000) (-105770599 / 1000000000) (Real.log (899631 / 1000000)) := by
  have h := reflection_log_6837_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6838_neg : (10125021 / 1000000000) ≤ -Real.log (989926063839 / 1000000000000) ∧
    -Real.log (989926063839 / 1000000000000) ≤ (5062511 / 500000000) := by
  have h := checkLog_sound (w := (10073936161 / 1989926063839)) (n := 12)
    (lo := (10125021 / 1000000000)) (hi := (5062511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989926063839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989926063839) = 1/(989926063839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6838 : Bounds (-5062511 / 500000000) (-10125021 / 1000000000) (Real.log (989926063839 / 1000000000000)) := by
  have h := reflection_log_6838_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6839_neg : (10074593 / 1000000000) ≤ -Real.log (618734991 / 625000000) ∧
    -Real.log (618734991 / 625000000) ≤ (5037297 / 500000000) := by
  have h := checkLog_sound (w := (6265009 / 1243734991)) (n := 12)
    (lo := (10074593 / 1000000000)) (hi := (5037297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 618734991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 618734991) = 1/(618734991 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6839 : Bounds (-5037297 / 500000000) (-10074593 / 1000000000) (Real.log (618734991 / 625000000)) := by
  have h := reflection_log_6839_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6840_neg : (100456561 / 500000000) ≤ -Real.log (250000000000 / 305629639507) ∧
    -Real.log (250000000000 / 305629639507) ≤ (200913123 / 1000000000) := by
  have h := checkLog_sound (w := (55629639507 / 555629639507)) (n := 12)
    (lo := (100456561 / 500000000)) (hi := (200913123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305629639507 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305629639507 / 250000000000) = 1/(250000000000 / 305629639507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6840 : Bounds (100456561 / 500000000) (200913123 / 1000000000) (Real.log (305629639507 / 250000000000)) := by
  have h := reflection_log_6840_neg
  have he : Real.log (305629639507 / 250000000000) = -Real.log (250000000000 / 305629639507) := by
    rw [show ((305629639507 / 250000000000) : ℝ) = ((250000000000 / 305629639507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6841_neg : (201416177 / 1000000000) ≤ -Real.log (250000000000 / 305783426761) ∧
    -Real.log (250000000000 / 305783426761) ≤ (100708089 / 500000000) := by
  have h := checkLog_sound (w := (55783426761 / 555783426761)) (n := 12)
    (lo := (201416177 / 1000000000)) (hi := (100708089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305783426761 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305783426761 / 250000000000) = 1/(250000000000 / 305783426761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6841 : Bounds (201416177 / 1000000000) (100708089 / 500000000) (Real.log (305783426761 / 250000000000)) := by
  have h := reflection_log_6841_neg
  have he : Real.log (305783426761 / 250000000000) = -Real.log (250000000000 / 305783426761) := by
    rw [show ((305783426761 / 250000000000) : ℝ) = ((250000000000 / 305783426761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6842_neg : (403382207 / 1000000000) ≤ -Real.log (250000000000 / 374219725343) ∧
    -Real.log (250000000000 / 374219725343) ≤ (6302847 / 15625000) := by
  have h := checkLog_sound (w := (124219725343 / 624219725343)) (n := 12)
    (lo := (403382207 / 1000000000)) (hi := (6302847 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374219725343 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374219725343 / 250000000000) = 1/(250000000000 / 374219725343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6842 : Bounds (403382207 / 1000000000) (6302847 / 15625000) (Real.log (374219725343 / 250000000000)) := by
  have h := reflection_log_6842_neg
  have he : Real.log (374219725343 / 250000000000) = -Real.log (250000000000 / 374219725343) := by
    rw [show ((374219725343 / 250000000000) : ℝ) = ((250000000000 / 374219725343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6843_neg : (403590459 / 1000000000) ≤ -Real.log (250000000000 / 374297665127) ∧
    -Real.log (250000000000 / 374297665127) ≤ (20179523 / 50000000) := by
  have h := checkLog_sound (w := (124297665127 / 624297665127)) (n := 12)
    (lo := (403590459 / 1000000000)) (hi := (20179523 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374297665127 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374297665127 / 250000000000) = 1/(250000000000 / 374297665127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6843 : Bounds (403590459 / 1000000000) (20179523 / 50000000) (Real.log (374297665127 / 250000000000)) := by
  have h := reflection_log_6843_neg
  have he : Real.log (374297665127 / 250000000000) = -Real.log (250000000000 / 374297665127) := by
    rw [show ((374297665127 / 250000000000) : ℝ) = ((250000000000 / 374297665127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6844_neg : (181654667 / 1000000000) ≤ -Real.log (1250 / 1499) ∧
    -Real.log (1250 / 1499) ≤ (45413667 / 250000000) := by
  have h := checkLog_sound (w := (249 / 2749)) (n := 12)
    (lo := (181654667 / 1000000000)) (hi := (45413667 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1499 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1499 / 1250) = 1/(1250 / 1499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6844 : Bounds (181654667 / 1000000000) (45413667 / 250000000) (Real.log (1499 / 1250)) := by
  have h := reflection_log_6844_neg
  have he : Real.log (1499 / 1250) = -Real.log (1250 / 1499) := by
    rw [show ((1499 / 1250) : ℝ) = ((1250 / 1499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6845_neg : (4442881 / 20000000) ≤ -Real.log (1001 / 1250) ∧
    -Real.log (1001 / 1250) ≤ (222144051 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 2251)) (n := 12)
    (lo := (4442881 / 20000000)) (hi := (222144051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1001) = 1/(1001 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6845 : Bounds (-222144051 / 1000000000) (-4442881 / 20000000) (Real.log (1001 / 1250)) := by
  have h := reflection_log_6845_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6846_neg : (9959 / 50000000) ≤ -Real.log (1250000 / 1250249) ∧
    -Real.log (1250000 / 1250249) ≤ (199181 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 2500249)) (n := 12)
    (lo := (9959 / 50000000)) (hi := (199181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250249 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250249 / 1250000) = 1/(1250000 / 1250249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6846 : Bounds (9959 / 50000000) (199181 / 1000000000) (Real.log (1250249 / 1250000)) := by
  have h := reflection_log_6846_neg
  have he : Real.log (1250249 / 1250000) = -Real.log (1250000 / 1250249) := by
    rw [show ((1250249 / 1250000) : ℝ) = ((1250000 / 1250249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6847_neg : (199219 / 1000000000) ≤ -Real.log (1249751 / 1250000) ∧
    -Real.log (1249751 / 1250000) ≤ (9961 / 50000000) := by
  have h := checkLog_sound (w := (249 / 2499751)) (n := 12)
    (lo := (199219 / 1000000000)) (hi := (9961 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249751) = 1/(1249751 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6847 : Bounds (-9961 / 50000000) (-199219 / 1000000000) (Real.log (1249751 / 1250000)) := by
  have h := reflection_log_6847_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
