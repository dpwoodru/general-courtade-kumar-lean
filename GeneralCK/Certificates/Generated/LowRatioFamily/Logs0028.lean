import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1792_neg : (178050689 / 1000000000) ≤ -Real.log (8369 / 10000) ∧
    -Real.log (8369 / 10000) ≤ (17805069 / 100000000) := by
  have h := checkLog_sound (w := (1631 / 18369)) (n := 12)
    (lo := (178050689 / 1000000000)) (hi := (17805069 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8369) = 1/(8369 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1792 : Bounds (-17805069 / 100000000) (-178050689 / 1000000000) (Real.log (8369 / 10000)) := by
  have h := reflection_log_1792_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1793_neg : (81543 / 500000000) ≤ -Real.log (10000000 / 10001631) ∧
    -Real.log (10000000 / 10001631) ≤ (163087 / 1000000000) := by
  have h := checkLog_sound (w := (1631 / 20001631)) (n := 12)
    (lo := (81543 / 500000000)) (hi := (163087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001631 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001631 / 10000000) = 1/(10000000 / 10001631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1793 : Bounds (81543 / 500000000) (163087 / 1000000000) (Real.log (10001631 / 10000000)) := by
  have h := reflection_log_1793_neg
  have he : Real.log (10001631 / 10000000) = -Real.log (10000000 / 10001631) := by
    rw [show ((10001631 / 10000000) : ℝ) = ((10000000 / 10001631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1794_neg : (163113 / 1000000000) ≤ -Real.log (9998369 / 10000000) ∧
    -Real.log (9998369 / 10000000) ≤ (81557 / 500000000) := by
  have h := checkLog_sound (w := (1631 / 19998369)) (n := 12)
    (lo := (163113 / 1000000000)) (hi := (81557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998369) = 1/(9998369 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1794 : Bounds (-81557 / 500000000) (-163113 / 1000000000) (Real.log (9998369 / 10000000)) := by
  have h := reflection_log_1794_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1795_neg : (78637413 / 1000000000) ≤ -Real.log (250000 / 270453) ∧
    -Real.log (250000 / 270453) ≤ (39318707 / 500000000) := by
  have h := checkLog_sound (w := (20453 / 520453)) (n := 12)
    (lo := (78637413 / 1000000000)) (hi := (39318707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270453 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270453 / 250000) = 1/(250000 / 270453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1795 : Bounds (78637413 / 1000000000) (39318707 / 500000000) (Real.log (270453 / 250000)) := by
  have h := reflection_log_1795_neg
  have he : Real.log (270453 / 250000) = -Real.log (250000 / 270453) := by
    rw [show ((270453 / 250000) : ℝ) = ((250000 / 270453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1796_neg : (21338279 / 250000000) ≤ -Real.log (229547 / 250000) ∧
    -Real.log (229547 / 250000) ≤ (85353117 / 1000000000) := by
  have h := checkLog_sound (w := (20453 / 479547)) (n := 12)
    (lo := (21338279 / 250000000)) (hi := (85353117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229547) = 1/(229547 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1796 : Bounds (-85353117 / 1000000000) (-21338279 / 250000000) (Real.log (229547 / 250000)) := by
  have h := reflection_log_1796_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1797_neg : (78835209 / 1000000000) ≤ -Real.log (500000 / 541013) ∧
    -Real.log (500000 / 541013) ≤ (7883521 / 100000000) := by
  have h := checkLog_sound (w := (41013 / 1041013)) (n := 12)
    (lo := (78835209 / 1000000000)) (hi := (7883521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541013 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541013 / 500000) = 1/(500000 / 541013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1797 : Bounds (78835209 / 1000000000) (7883521 / 100000000) (Real.log (541013 / 500000)) := by
  have h := reflection_log_1797_neg
  have he : Real.log (541013 / 500000) = -Real.log (500000 / 541013) := by
    rw [show ((541013 / 500000) : ℝ) = ((500000 / 541013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1798_neg : (85586211 / 1000000000) ≤ -Real.log (458987 / 500000) ∧
    -Real.log (458987 / 500000) ≤ (21396553 / 250000000) := by
  have h := checkLog_sound (w := (41013 / 958987)) (n := 12)
    (lo := (85586211 / 1000000000)) (hi := (21396553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458987) = 1/(458987 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1798 : Bounds (-21396553 / 250000000) (-85586211 / 1000000000) (Real.log (458987 / 500000)) := by
  have h := reflection_log_1798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1799_neg : (6751001 / 1000000000) ≤ -Real.log (248317933831 / 250000000000) ∧
    -Real.log (248317933831 / 250000000000) ≤ (3375501 / 500000000) := by
  have h := checkLog_sound (w := (1682066169 / 498317933831)) (n := 12)
    (lo := (6751001 / 1000000000)) (hi := (3375501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248317933831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248317933831) = 1/(248317933831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1799 : Bounds (-3375501 / 500000000) (-6751001 / 1000000000) (Real.log (248317933831 / 250000000000)) := by
  have h := reflection_log_1799_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1800_neg : (6715703 / 1000000000) ≤ -Real.log (62081674791 / 62500000000) ∧
    -Real.log (62081674791 / 62500000000) ≤ (839463 / 125000000) := by
  have h := checkLog_sound (w := (418325209 / 124581674791)) (n := 12)
    (lo := (6715703 / 1000000000)) (hi := (839463 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62081674791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62081674791) = 1/(62081674791 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1800 : Bounds (-839463 / 125000000) (-6715703 / 1000000000) (Real.log (62081674791 / 62500000000)) := by
  have h := reflection_log_1800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1801_neg : (163990529 / 1000000000) ≤ -Real.log (250000000000 / 294550789163) ∧
    -Real.log (250000000000 / 294550789163) ≤ (16399053 / 100000000) := by
  have h := checkLog_sound (w := (44550789163 / 544550789163)) (n := 12)
    (lo := (163990529 / 1000000000)) (hi := (16399053 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294550789163 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294550789163 / 250000000000) = 1/(250000000000 / 294550789163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1801 : Bounds (163990529 / 1000000000) (16399053 / 100000000) (Real.log (294550789163 / 250000000000)) := by
  have h := reflection_log_1801_neg
  have he : Real.log (294550789163 / 250000000000) = -Real.log (250000000000 / 294550789163) := by
    rw [show ((294550789163 / 250000000000) : ℝ) = ((250000000000 / 294550789163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1802_neg : (8221071 / 50000000) ≤ -Real.log (250000000000 / 294677735971) ∧
    -Real.log (250000000000 / 294677735971) ≤ (164421421 / 1000000000) := by
  have h := checkLog_sound (w := (44677735971 / 544677735971)) (n := 12)
    (lo := (8221071 / 50000000)) (hi := (164421421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294677735971 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294677735971 / 250000000000) = 1/(250000000000 / 294677735971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1802 : Bounds (8221071 / 50000000) (164421421 / 1000000000) (Real.log (294677735971 / 250000000000)) := by
  have h := reflection_log_1802_neg
  have he : Real.log (294677735971 / 250000000000) = -Real.log (250000000000 / 294677735971) := by
    rw [show ((294677735971 / 250000000000) : ℝ) = ((250000000000 / 294677735971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1803_neg : (164467041 / 500000000) ≤ -Real.log (500000000000 / 694743130227) ∧
    -Real.log (500000000000 / 694743130227) ≤ (328934083 / 1000000000) := by
  have h := checkLog_sound (w := (194743130227 / 1194743130227)) (n := 12)
    (lo := (164467041 / 500000000)) (hi := (328934083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694743130227 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694743130227 / 500000000000) = 1/(500000000000 / 694743130227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1803 : Bounds (164467041 / 500000000) (328934083 / 1000000000) (Real.log (694743130227 / 500000000000)) := by
  have h := reflection_log_1803_neg
  have he : Real.log (694743130227 / 500000000000) = -Real.log (500000000000 / 694743130227) := by
    rw [show ((694743130227 / 500000000000) : ℝ) = ((500000000000 / 694743130227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1804_neg : (41142443 / 125000000) ≤ -Real.log (250000000000 / 347442944199) ∧
    -Real.log (250000000000 / 347442944199) ≤ (65827909 / 200000000) := by
  have h := checkLog_sound (w := (97442944199 / 597442944199)) (n := 12)
    (lo := (41142443 / 125000000)) (hi := (65827909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347442944199 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347442944199 / 250000000000) = 1/(250000000000 / 347442944199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1804 : Bounds (41142443 / 125000000) (65827909 / 200000000) (Real.log (347442944199 / 250000000000)) := by
  have h := reflection_log_1804_neg
  have he : Real.log (347442944199 / 250000000000) = -Real.log (250000000000 / 347442944199) := by
    rw [show ((347442944199 / 250000000000) : ℝ) = ((250000000000 / 347442944199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1805_neg : (151174827 / 1000000000) ≤ -Real.log (625 / 727) ∧
    -Real.log (625 / 727) ≤ (37793707 / 250000000) := by
  have h := checkLog_sound (w := (51 / 676)) (n := 12)
    (lo := (151174827 / 1000000000)) (hi := (37793707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727 / 625) = 1/(625 / 727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1805 : Bounds (151174827 / 1000000000) (37793707 / 250000000) (Real.log (727 / 625)) := by
  have h := reflection_log_1805_neg
  have he : Real.log (727 / 625) = -Real.log (625 / 727) := by
    rw [show ((727 / 625) : ℝ) = ((625 / 727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1806_neg : (35634037 / 200000000) ≤ -Real.log (523 / 625) ∧
    -Real.log (523 / 625) ≤ (89085093 / 500000000) := by
  have h := checkLog_sound (w := (51 / 574)) (n := 12)
    (lo := (35634037 / 200000000)) (hi := (89085093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 523) = 1/(523 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1806 : Bounds (-89085093 / 500000000) (-35634037 / 200000000) (Real.log (523 / 625)) := by
  have h := reflection_log_1806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1807_neg : (81593 / 500000000) ≤ -Real.log (312500 / 312551) ∧
    -Real.log (312500 / 312551) ≤ (163187 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 625051)) (n := 12)
    (lo := (81593 / 500000000)) (hi := (163187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312551 / 312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312551 / 312500) = 1/(312500 / 312551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1807 : Bounds (81593 / 500000000) (163187 / 1000000000) (Real.log (312551 / 312500)) := by
  have h := reflection_log_1807_neg
  have he : Real.log (312551 / 312500) = -Real.log (312500 / 312551) := by
    rw [show ((312551 / 312500) : ℝ) = ((312500 / 312551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1808_neg : (163213 / 1000000000) ≤ -Real.log (312449 / 312500) ∧
    -Real.log (312449 / 312500) ≤ (81607 / 500000000) := by
  have h := checkLog_sound (w := (51 / 624949)) (n := 12)
    (lo := (163213 / 1000000000)) (hi := (81607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312500 / 312449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312500 / 312449) = 1/(312449 / 312500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1808 : Bounds (-81607 / 500000000) (-163213 / 1000000000) (Real.log (312449 / 312500)) := by
  have h := reflection_log_1808_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1809_neg : (15736911 / 200000000) ≤ -Real.log (1000000 / 1081863) ∧
    -Real.log (1000000 / 1081863) ≤ (19671139 / 250000000) := by
  have h := checkLog_sound (w := (81863 / 2081863)) (n := 12)
    (lo := (15736911 / 200000000)) (hi := (19671139 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081863 / 1000000) = 1/(1000000 / 1081863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1809 : Bounds (15736911 / 200000000) (19671139 / 250000000) (Real.log (1081863 / 1000000)) := by
  have h := reflection_log_1809_neg
  have he : Real.log (1081863 / 1000000) = -Real.log (1000000 / 1081863) := by
    rw [show ((1081863 / 1000000) : ℝ) = ((1000000 / 1081863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1810_neg : (42704331 / 500000000) ≤ -Real.log (918137 / 1000000) ∧
    -Real.log (918137 / 1000000) ≤ (85408663 / 1000000000) := by
  have h := checkLog_sound (w := (81863 / 1918137)) (n := 12)
    (lo := (42704331 / 500000000)) (hi := (85408663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918137) = 1/(918137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1810 : Bounds (-85408663 / 1000000000) (-42704331 / 500000000) (Real.log (918137 / 1000000)) := by
  have h := reflection_log_1810_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1811_neg : (39441171 / 500000000) ≤ -Real.log (1000000 / 1082077) ∧
    -Real.log (1000000 / 1082077) ≤ (78882343 / 1000000000) := by
  have h := checkLog_sound (w := (82077 / 2082077)) (n := 12)
    (lo := (39441171 / 500000000)) (hi := (78882343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082077 / 1000000) = 1/(1000000 / 1082077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1811 : Bounds (39441171 / 500000000) (78882343 / 1000000000) (Real.log (1082077 / 1000000)) := by
  have h := reflection_log_1811_neg
  have he : Real.log (1082077 / 1000000) = -Real.log (1000000 / 1082077) := by
    rw [show ((1082077 / 1000000) : ℝ) = ((1000000 / 1082077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1812_neg : (85641769 / 1000000000) ≤ -Real.log (917923 / 1000000) ∧
    -Real.log (917923 / 1000000) ≤ (8564177 / 100000000) := by
  have h := checkLog_sound (w := (82077 / 1917923)) (n := 12)
    (lo := (85641769 / 1000000000)) (hi := (8564177 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917923) = 1/(917923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1812 : Bounds (-8564177 / 100000000) (-85641769 / 1000000000) (Real.log (917923 / 1000000)) := by
  have h := reflection_log_1812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1813_neg : (6759427 / 1000000000) ≤ -Real.log (993263366071 / 1000000000000) ∧
    -Real.log (993263366071 / 1000000000000) ≤ (1689857 / 250000000) := by
  have h := checkLog_sound (w := (6736633929 / 1993263366071)) (n := 12)
    (lo := (6759427 / 1000000000)) (hi := (1689857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993263366071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993263366071) = 1/(993263366071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1813 : Bounds (-1689857 / 250000000) (-6759427 / 1000000000) (Real.log (993263366071 / 1000000000000)) := by
  have h := reflection_log_1813_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1814_neg : (3362053 / 500000000) ≤ -Real.log (993298449231 / 1000000000000) ∧
    -Real.log (993298449231 / 1000000000000) ≤ (6724107 / 1000000000) := by
  have h := checkLog_sound (w := (6701550769 / 1993298449231)) (n := 12)
    (lo := (3362053 / 500000000)) (hi := (6724107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993298449231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993298449231) = 1/(993298449231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1814 : Bounds (-6724107 / 1000000000) (-3362053 / 500000000) (Real.log (993298449231 / 1000000000000)) := by
  have h := reflection_log_1814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1815_neg : (164093217 / 1000000000) ≤ -Real.log (25000000000 / 29458103747) ∧
    -Real.log (25000000000 / 29458103747) ≤ (82046609 / 500000000) := by
  have h := checkLog_sound (w := (4458103747 / 54458103747)) (n := 12)
    (lo := (164093217 / 1000000000)) (hi := (82046609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29458103747 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29458103747 / 25000000000) = 1/(25000000000 / 29458103747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1815 : Bounds (164093217 / 1000000000) (82046609 / 500000000) (Real.log (29458103747 / 25000000000)) := by
  have h := reflection_log_1815_neg
  have he : Real.log (29458103747 / 25000000000) = -Real.log (25000000000 / 29458103747) := by
    rw [show ((29458103747 / 25000000000) : ℝ) = ((25000000000 / 29458103747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1816_neg : (10282757 / 62500000) ≤ -Real.log (500000000000 / 589415996767) ∧
    -Real.log (500000000000 / 589415996767) ≤ (164524113 / 1000000000) := by
  have h := checkLog_sound (w := (89415996767 / 1089415996767)) (n := 12)
    (lo := (10282757 / 62500000)) (hi := (164524113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589415996767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589415996767 / 500000000000) = 1/(500000000000 / 589415996767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1816 : Bounds (10282757 / 62500000) (164524113 / 1000000000) (Real.log (589415996767 / 500000000000)) := by
  have h := reflection_log_1816_neg
  have he : Real.log (589415996767 / 500000000000) = -Real.log (500000000000 / 589415996767) := by
    rw [show ((589415996767 / 500000000000) : ℝ) = ((500000000000 / 589415996767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1817_neg : (41142443 / 125000000) ≤ -Real.log (500000000000 / 694885888397) ∧
    -Real.log (500000000000 / 694885888397) ≤ (65827909 / 200000000) := by
  have h := checkLog_sound (w := (194885888397 / 1194885888397)) (n := 12)
    (lo := (41142443 / 125000000)) (hi := (65827909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694885888397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694885888397 / 500000000000) = 1/(500000000000 / 694885888397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1817 : Bounds (41142443 / 125000000) (65827909 / 200000000) (Real.log (694885888397 / 500000000000)) := by
  have h := reflection_log_1817_neg
  have he : Real.log (694885888397 / 500000000000) = -Real.log (500000000000 / 694885888397) := by
    rw [show ((694885888397 / 500000000000) : ℝ) = ((500000000000 / 694885888397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1818_neg : (329345013 / 1000000000) ≤ -Real.log (500000000000 / 695028680689) ∧
    -Real.log (500000000000 / 695028680689) ≤ (164672507 / 500000000) := by
  have h := checkLog_sound (w := (195028680689 / 1195028680689)) (n := 12)
    (lo := (329345013 / 1000000000)) (hi := (164672507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695028680689 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695028680689 / 500000000000) = 1/(500000000000 / 695028680689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1818 : Bounds (329345013 / 1000000000) (164672507 / 500000000) (Real.log (695028680689 / 500000000000)) := by
  have h := reflection_log_1818_neg
  have he : Real.log (695028680689 / 500000000000) = -Real.log (500000000000 / 695028680689) := by
    rw [show ((695028680689 / 500000000000) : ℝ) = ((500000000000 / 695028680689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1819_neg : (151260793 / 1000000000) ≤ -Real.log (10000 / 11633) ∧
    -Real.log (10000 / 11633) ≤ (75630397 / 500000000) := by
  have h := checkLog_sound (w := (1633 / 21633)) (n := 12)
    (lo := (151260793 / 1000000000)) (hi := (75630397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11633 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11633 / 10000) = 1/(10000 / 11633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1819 : Bounds (151260793 / 1000000000) (75630397 / 500000000) (Real.log (11633 / 10000)) := by
  have h := reflection_log_1819_neg
  have he : Real.log (11633 / 10000) = -Real.log (10000 / 11633) := by
    rw [show ((11633 / 10000) : ℝ) = ((10000 / 11633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1820_neg : (35657939 / 200000000) ≤ -Real.log (8367 / 10000) ∧
    -Real.log (8367 / 10000) ≤ (5571553 / 31250000) := by
  have h := checkLog_sound (w := (1633 / 18367)) (n := 12)
    (lo := (35657939 / 200000000)) (hi := (5571553 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8367) = 1/(8367 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1820 : Bounds (-5571553 / 31250000) (-35657939 / 200000000) (Real.log (8367 / 10000)) := by
  have h := reflection_log_1820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1821_neg : (81643 / 500000000) ≤ -Real.log (10000000 / 10001633) ∧
    -Real.log (10000000 / 10001633) ≤ (163287 / 1000000000) := by
  have h := checkLog_sound (w := (1633 / 20001633)) (n := 12)
    (lo := (81643 / 500000000)) (hi := (163287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001633 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001633 / 10000000) = 1/(10000000 / 10001633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1821 : Bounds (81643 / 500000000) (163287 / 1000000000) (Real.log (10001633 / 10000000)) := by
  have h := reflection_log_1821_neg
  have he : Real.log (10001633 / 10000000) = -Real.log (10000000 / 10001633) := by
    rw [show ((10001633 / 10000000) : ℝ) = ((10000000 / 10001633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1822_neg : (163313 / 1000000000) ≤ -Real.log (9998367 / 10000000) ∧
    -Real.log (9998367 / 10000000) ≤ (81657 / 500000000) := by
  have h := checkLog_sound (w := (1633 / 19998367)) (n := 12)
    (lo := (163313 / 1000000000)) (hi := (81657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998367) = 1/(9998367 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1822 : Bounds (-81657 / 500000000) (-163313 / 1000000000) (Real.log (9998367 / 10000000)) := by
  have h := reflection_log_1822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1823_neg : (7873077 / 100000000) ≤ -Real.log (1000000 / 1081913) ∧
    -Real.log (1000000 / 1081913) ≤ (78730771 / 1000000000) := by
  have h := checkLog_sound (w := (81913 / 2081913)) (n := 12)
    (lo := (7873077 / 100000000)) (hi := (78730771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081913 / 1000000) = 1/(1000000 / 1081913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1823 : Bounds (7873077 / 100000000) (78730771 / 1000000000) (Real.log (1081913 / 1000000)) := by
  have h := reflection_log_1823_neg
  have he : Real.log (1081913 / 1000000) = -Real.log (1000000 / 1081913) := by
    rw [show ((1081913 / 1000000) : ℝ) = ((1000000 / 1081913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1824_neg : (85463121 / 1000000000) ≤ -Real.log (918087 / 1000000) ∧
    -Real.log (918087 / 1000000) ≤ (42731561 / 500000000) := by
  have h := checkLog_sound (w := (81913 / 1918087)) (n := 12)
    (lo := (85463121 / 1000000000)) (hi := (42731561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918087) = 1/(918087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1824 : Bounds (-42731561 / 500000000) (-85463121 / 1000000000) (Real.log (918087 / 1000000)) := by
  have h := reflection_log_1824_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1825_neg : (1233273 / 15625000) ≤ -Real.log (62500 / 67633) ∧
    -Real.log (62500 / 67633) ≤ (78929473 / 1000000000) := by
  have h := checkLog_sound (w := (5133 / 130133)) (n := 12)
    (lo := (1233273 / 15625000)) (hi := (78929473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67633 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67633 / 62500) = 1/(62500 / 67633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1825 : Bounds (1233273 / 15625000) (78929473 / 1000000000) (Real.log (67633 / 62500)) := by
  have h := reflection_log_1825_neg
  have he : Real.log (67633 / 62500) = -Real.log (62500 / 67633) := by
    rw [show ((67633 / 62500) : ℝ) = ((62500 / 67633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1826_neg : (85697331 / 1000000000) ≤ -Real.log (57367 / 62500) ∧
    -Real.log (57367 / 62500) ≤ (21424333 / 250000000) := by
  have h := checkLog_sound (w := (5133 / 119867)) (n := 12)
    (lo := (85697331 / 1000000000)) (hi := (21424333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57367) = 1/(57367 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1826 : Bounds (-21424333 / 250000000) (-85697331 / 1000000000) (Real.log (57367 / 62500)) := by
  have h := reflection_log_1826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1827_neg : (3383929 / 500000000) ≤ -Real.log (3879902311 / 3906250000) ∧
    -Real.log (3879902311 / 3906250000) ≤ (6767859 / 1000000000) := by
  have h := checkLog_sound (w := (26347689 / 7786152311)) (n := 12)
    (lo := (3383929 / 500000000)) (hi := (6767859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3879902311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3879902311) = 1/(3879902311 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1827 : Bounds (-6767859 / 1000000000) (-3383929 / 500000000) (Real.log (3879902311 / 3906250000)) := by
  have h := reflection_log_1827_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1828_neg : (6732351 / 1000000000) ≤ -Real.log (993290260431 / 1000000000000) ∧
    -Real.log (993290260431 / 1000000000000) ≤ (105193 / 15625000) := by
  have h := checkLog_sound (w := (6709739569 / 1993290260431)) (n := 12)
    (lo := (6732351 / 1000000000)) (hi := (105193 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993290260431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993290260431) = 1/(993290260431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1828 : Bounds (-105193 / 15625000) (-6732351 / 1000000000) (Real.log (993290260431 / 1000000000000)) := by
  have h := reflection_log_1828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1829_neg : (41048473 / 250000000) ≤ -Real.log (976562500 / 1150823031) ∧
    -Real.log (976562500 / 1150823031) ≤ (164193893 / 1000000000) := by
  have h := checkLog_sound (w := (174260531 / 2127385531)) (n := 12)
    (lo := (41048473 / 250000000)) (hi := (164193893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150823031 / 976562500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150823031 / 976562500) = 1/(976562500 / 1150823031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1829 : Bounds (41048473 / 250000000) (164193893 / 1000000000) (Real.log (1150823031 / 976562500)) := by
  have h := reflection_log_1829_neg
  have he : Real.log (1150823031 / 976562500) = -Real.log (976562500 / 1150823031) := by
    rw [show ((1150823031 / 976562500) : ℝ) = ((976562500 / 1150823031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1830_neg : (41156701 / 250000000) ≤ -Real.log (250000000000 / 294738264159) ∧
    -Real.log (250000000000 / 294738264159) ≤ (32925361 / 200000000) := by
  have h := checkLog_sound (w := (44738264159 / 544738264159)) (n := 12)
    (lo := (41156701 / 250000000)) (hi := (32925361 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294738264159 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294738264159 / 250000000000) = 1/(250000000000 / 294738264159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1830 : Bounds (41156701 / 250000000) (32925361 / 200000000) (Real.log (294738264159 / 250000000000)) := by
  have h := reflection_log_1830_neg
  have he : Real.log (294738264159 / 250000000000) = -Real.log (250000000000 / 294738264159) := by
    rw [show ((294738264159 / 250000000000) : ℝ) = ((250000000000 / 294738264159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1831_neg : (329345013 / 1000000000) ≤ -Real.log (31250000000 / 43439292543) ∧
    -Real.log (31250000000 / 43439292543) ≤ (164672507 / 500000000) := by
  have h := checkLog_sound (w := (12189292543 / 74689292543)) (n := 12)
    (lo := (329345013 / 1000000000)) (hi := (164672507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43439292543 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43439292543 / 31250000000) = 1/(31250000000 / 43439292543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1831 : Bounds (329345013 / 1000000000) (164672507 / 500000000) (Real.log (43439292543 / 31250000000)) := by
  have h := reflection_log_1831_neg
  have he : Real.log (43439292543 / 31250000000) = -Real.log (31250000000 / 43439292543) := by
    rw [show ((43439292543 / 31250000000) : ℝ) = ((31250000000 / 43439292543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1832_neg : (329550489 / 1000000000) ≤ -Real.log (62500000000 / 86896438389) ∧
    -Real.log (62500000000 / 86896438389) ≤ (32955049 / 100000000) := by
  have h := checkLog_sound (w := (24396438389 / 149396438389)) (n := 12)
    (lo := (329550489 / 1000000000)) (hi := (32955049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86896438389 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86896438389 / 62500000000) = 1/(62500000000 / 86896438389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1832 : Bounds (329550489 / 1000000000) (32955049 / 100000000) (Real.log (86896438389 / 62500000000)) := by
  have h := reflection_log_1832_neg
  have he : Real.log (86896438389 / 62500000000) = -Real.log (62500000000 / 86896438389) := by
    rw [show ((86896438389 / 62500000000) : ℝ) = ((62500000000 / 86896438389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1833_neg : (2364793 / 15625000) ≤ -Real.log (5000 / 5817) ∧
    -Real.log (5000 / 5817) ≤ (151346753 / 1000000000) := by
  have h := checkLog_sound (w := (817 / 10817)) (n := 12)
    (lo := (2364793 / 15625000)) (hi := (151346753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5817 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5817 / 5000) = 1/(5000 / 5817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1833 : Bounds (2364793 / 15625000) (151346753 / 1000000000) (Real.log (5817 / 5000)) := by
  have h := reflection_log_1833_neg
  have he : Real.log (5817 / 5000) = -Real.log (5000 / 5817) := by
    rw [show ((5817 / 5000) : ℝ) = ((5000 / 5817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1834_neg : (178409219 / 1000000000) ≤ -Real.log (4183 / 5000) ∧
    -Real.log (4183 / 5000) ≤ (8920461 / 50000000) := by
  have h := checkLog_sound (w := (817 / 9183)) (n := 12)
    (lo := (178409219 / 1000000000)) (hi := (8920461 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4183) = 1/(4183 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1834 : Bounds (-8920461 / 50000000) (-178409219 / 1000000000) (Real.log (4183 / 5000)) := by
  have h := reflection_log_1834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1835_neg : (81693 / 500000000) ≤ -Real.log (5000000 / 5000817) ∧
    -Real.log (5000000 / 5000817) ≤ (163387 / 1000000000) := by
  have h := checkLog_sound (w := (817 / 10000817)) (n := 12)
    (lo := (81693 / 500000000)) (hi := (163387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000817 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000817 / 5000000) = 1/(5000000 / 5000817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1835 : Bounds (81693 / 500000000) (163387 / 1000000000) (Real.log (5000817 / 5000000)) := by
  have h := reflection_log_1835_neg
  have he : Real.log (5000817 / 5000000) = -Real.log (5000000 / 5000817) := by
    rw [show ((5000817 / 5000000) : ℝ) = ((5000000 / 5000817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1836_neg : (163413 / 1000000000) ≤ -Real.log (4999183 / 5000000) ∧
    -Real.log (4999183 / 5000000) ≤ (81707 / 500000000) := by
  have h := checkLog_sound (w := (817 / 9999183)) (n := 12)
    (lo := (163413 / 1000000000)) (hi := (81707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999183) = 1/(4999183 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1836 : Bounds (-81707 / 500000000) (-163413 / 1000000000) (Real.log (4999183 / 5000000)) := by
  have h := reflection_log_1836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1837_neg : (19694477 / 250000000) ≤ -Real.log (250000 / 270491) ∧
    -Real.log (250000 / 270491) ≤ (78777909 / 1000000000) := by
  have h := checkLog_sound (w := (20491 / 520491)) (n := 12)
    (lo := (19694477 / 250000000)) (hi := (78777909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270491 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270491 / 250000) = 1/(250000 / 270491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1837 : Bounds (19694477 / 250000000) (78777909 / 1000000000) (Real.log (270491 / 250000)) := by
  have h := reflection_log_1837_neg
  have he : Real.log (270491 / 250000) = -Real.log (250000 / 270491) := by
    rw [show ((270491 / 250000) : ℝ) = ((250000 / 270491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1838_neg : (85518673 / 1000000000) ≤ -Real.log (229509 / 250000) ∧
    -Real.log (229509 / 250000) ≤ (42759337 / 500000000) := by
  have h := checkLog_sound (w := (20491 / 479509)) (n := 12)
    (lo := (85518673 / 1000000000)) (hi := (42759337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229509) = 1/(229509 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1838 : Bounds (-42759337 / 500000000) (-85518673 / 1000000000) (Real.log (229509 / 250000)) := by
  have h := reflection_log_1838_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1839_neg : (78975677 / 1000000000) ≤ -Real.log (500000 / 541089) ∧
    -Real.log (500000 / 541089) ≤ (39487839 / 500000000) := by
  have h := checkLog_sound (w := (41089 / 1041089)) (n := 12)
    (lo := (78975677 / 1000000000)) (hi := (39487839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541089 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541089 / 500000) = 1/(500000 / 541089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1839 : Bounds (78975677 / 1000000000) (39487839 / 500000000) (Real.log (541089 / 500000)) := by
  have h := reflection_log_1839_neg
  have he : Real.log (541089 / 500000) = -Real.log (500000 / 541089) := by
    rw [show ((541089 / 500000) : ℝ) = ((500000 / 541089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1840_neg : (42875903 / 500000000) ≤ -Real.log (458911 / 500000) ∧
    -Real.log (458911 / 500000) ≤ (85751807 / 1000000000) := by
  have h := checkLog_sound (w := (41089 / 958911)) (n := 12)
    (lo := (42875903 / 500000000)) (hi := (85751807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458911) = 1/(458911 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1840 : Bounds (-85751807 / 1000000000) (-42875903 / 500000000) (Real.log (458911 / 500000)) := by
  have h := reflection_log_1840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1841_neg : (6776129 / 1000000000) ≤ -Real.log (248311694079 / 250000000000) ∧
    -Real.log (248311694079 / 250000000000) ≤ (677613 / 100000000) := by
  have h := checkLog_sound (w := (1688305921 / 498311694079)) (n := 12)
    (lo := (6776129 / 1000000000)) (hi := (677613 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248311694079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248311694079) = 1/(248311694079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1841 : Bounds (-677613 / 100000000) (-6776129 / 1000000000) (Real.log (248311694079 / 250000000000)) := by
  have h := reflection_log_1841_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1842_neg : (1348153 / 200000000) ≤ -Real.log (62080118919 / 62500000000) ∧
    -Real.log (62080118919 / 62500000000) ≤ (3370383 / 500000000) := by
  have h := checkLog_sound (w := (419881081 / 124580118919)) (n := 12)
    (lo := (1348153 / 200000000)) (hi := (3370383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62080118919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62080118919) = 1/(62080118919 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1842 : Bounds (-3370383 / 500000000) (-1348153 / 200000000) (Real.log (62080118919 / 62500000000)) := by
  have h := reflection_log_1842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1843_neg : (164296581 / 1000000000) ≤ -Real.log (500000000000 / 589281901799) ∧
    -Real.log (500000000000 / 589281901799) ≤ (82148291 / 500000000) := by
  have h := checkLog_sound (w := (89281901799 / 1089281901799)) (n := 12)
    (lo := (164296581 / 1000000000)) (hi := (82148291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589281901799 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589281901799 / 500000000000) = 1/(500000000000 / 589281901799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1843 : Bounds (164296581 / 1000000000) (82148291 / 500000000) (Real.log (589281901799 / 500000000000)) := by
  have h := reflection_log_1843_neg
  have he : Real.log (589281901799 / 500000000000) = -Real.log (500000000000 / 589281901799) := by
    rw [show ((589281901799 / 500000000000) : ℝ) = ((500000000000 / 589281901799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1844_neg : (41181871 / 250000000) ≤ -Real.log (500000000000 / 589535879507) ∧
    -Real.log (500000000000 / 589535879507) ≤ (32945497 / 200000000) := by
  have h := checkLog_sound (w := (89535879507 / 1089535879507)) (n := 12)
    (lo := (41181871 / 250000000)) (hi := (32945497 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589535879507 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589535879507 / 500000000000) = 1/(500000000000 / 589535879507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1844 : Bounds (41181871 / 250000000) (32945497 / 200000000) (Real.log (589535879507 / 500000000000)) := by
  have h := reflection_log_1844_neg
  have he : Real.log (589535879507 / 500000000000) = -Real.log (500000000000 / 589535879507) := by
    rw [show ((589535879507 / 500000000000) : ℝ) = ((500000000000 / 589535879507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1845_neg : (329550489 / 1000000000) ≤ -Real.log (500000000000 / 695171507111) ∧
    -Real.log (500000000000 / 695171507111) ≤ (32955049 / 100000000) := by
  have h := checkLog_sound (w := (195171507111 / 1195171507111)) (n := 12)
    (lo := (329550489 / 1000000000)) (hi := (32955049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695171507111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695171507111 / 500000000000) = 1/(500000000000 / 695171507111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1845 : Bounds (329550489 / 1000000000) (32955049 / 100000000) (Real.log (695171507111 / 500000000000)) := by
  have h := reflection_log_1845_neg
  have he : Real.log (695171507111 / 500000000000) = -Real.log (500000000000 / 695171507111) := by
    rw [show ((695171507111 / 500000000000) : ℝ) = ((500000000000 / 695171507111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1846_neg : (82438993 / 250000000) ≤ -Real.log (500000000000 / 695314367679) ∧
    -Real.log (500000000000 / 695314367679) ≤ (329755973 / 1000000000) := by
  have h := checkLog_sound (w := (195314367679 / 1195314367679)) (n := 12)
    (lo := (82438993 / 250000000)) (hi := (329755973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695314367679 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695314367679 / 500000000000) = 1/(500000000000 / 695314367679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1846 : Bounds (82438993 / 250000000) (329755973 / 1000000000) (Real.log (695314367679 / 500000000000)) := by
  have h := reflection_log_1846_neg
  have he : Real.log (695314367679 / 500000000000) = -Real.log (500000000000 / 695314367679) := by
    rw [show ((695314367679 / 500000000000) : ℝ) = ((500000000000 / 695314367679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1847_neg : (151432703 / 1000000000) ≤ -Real.log (2000 / 2327) ∧
    -Real.log (2000 / 2327) ≤ (295767 / 1953125) := by
  have h := checkLog_sound (w := (327 / 4327)) (n := 12)
    (lo := (151432703 / 1000000000)) (hi := (295767 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2327 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2327 / 2000) = 1/(2000 / 2327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1847 : Bounds (151432703 / 1000000000) (295767 / 1953125) (Real.log (2327 / 2000)) := by
  have h := reflection_log_1847_neg
  have he : Real.log (2327 / 2000) = -Real.log (2000 / 2327) := by
    rw [show ((2327 / 2000) : ℝ) = ((2000 / 2327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1848_neg : (89264379 / 500000000) ≤ -Real.log (1673 / 2000) ∧
    -Real.log (1673 / 2000) ≤ (178528759 / 1000000000) := by
  have h := checkLog_sound (w := (327 / 3673)) (n := 12)
    (lo := (89264379 / 500000000)) (hi := (178528759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1673) = 1/(1673 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1848 : Bounds (-178528759 / 1000000000) (-89264379 / 500000000) (Real.log (1673 / 2000)) := by
  have h := reflection_log_1848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1849_neg : (81743 / 500000000) ≤ -Real.log (2000000 / 2000327) ∧
    -Real.log (2000000 / 2000327) ≤ (163487 / 1000000000) := by
  have h := checkLog_sound (w := (327 / 4000327)) (n := 12)
    (lo := (81743 / 500000000)) (hi := (163487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000327 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000327 / 2000000) = 1/(2000000 / 2000327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1849 : Bounds (81743 / 500000000) (163487 / 1000000000) (Real.log (2000327 / 2000000)) := by
  have h := reflection_log_1849_neg
  have he : Real.log (2000327 / 2000000) = -Real.log (2000000 / 2000327) := by
    rw [show ((2000327 / 2000000) : ℝ) = ((2000000 / 2000327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1850_neg : (163513 / 1000000000) ≤ -Real.log (1999673 / 2000000) ∧
    -Real.log (1999673 / 2000000) ≤ (81757 / 500000000) := by
  have h := checkLog_sound (w := (327 / 3999673)) (n := 12)
    (lo := (163513 / 1000000000)) (hi := (81757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999673) = 1/(1999673 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1850 : Bounds (-81757 / 500000000) (-163513 / 1000000000) (Real.log (1999673 / 2000000)) := by
  have h := reflection_log_1850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1851_neg : (78825043 / 1000000000) ≤ -Real.log (200000 / 216403) ∧
    -Real.log (200000 / 216403) ≤ (19706261 / 250000000) := by
  have h := checkLog_sound (w := (16403 / 416403)) (n := 12)
    (lo := (78825043 / 1000000000)) (hi := (19706261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216403 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216403 / 200000) = 1/(200000 / 216403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1851 : Bounds (78825043 / 1000000000) (19706261 / 250000000) (Real.log (216403 / 200000)) := by
  have h := reflection_log_1851_neg
  have he : Real.log (216403 / 200000) = -Real.log (200000 / 216403) := by
    rw [show ((216403 / 200000) : ℝ) = ((200000 / 216403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1852_neg : (21393557 / 250000000) ≤ -Real.log (183597 / 200000) ∧
    -Real.log (183597 / 200000) ≤ (85574229 / 1000000000) := by
  have h := checkLog_sound (w := (16403 / 383597)) (n := 12)
    (lo := (21393557 / 250000000)) (hi := (85574229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183597) = 1/(183597 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1852 : Bounds (-85574229 / 1000000000) (-21393557 / 250000000) (Real.log (183597 / 200000)) := by
  have h := reflection_log_1852_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1853_neg : (79022803 / 1000000000) ≤ -Real.log (1000000 / 1082229) ∧
    -Real.log (1000000 / 1082229) ≤ (19755701 / 250000000) := by
  have h := checkLog_sound (w := (82229 / 2082229)) (n := 12)
    (lo := (79022803 / 1000000000)) (hi := (19755701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082229 / 1000000) = 1/(1000000 / 1082229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1853 : Bounds (79022803 / 1000000000) (19755701 / 250000000) (Real.log (1082229 / 1000000)) := by
  have h := reflection_log_1853_neg
  have he : Real.log (1082229 / 1000000) = -Real.log (1000000 / 1082229) := by
    rw [show ((1082229 / 1000000) : ℝ) = ((1000000 / 1082229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1854_neg : (42903687 / 500000000) ≤ -Real.log (917771 / 1000000) ∧
    -Real.log (917771 / 1000000) ≤ (686459 / 8000000) := by
  have h := checkLog_sound (w := (82229 / 1917771)) (n := 12)
    (lo := (42903687 / 500000000)) (hi := (686459 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917771) = 1/(917771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1854 : Bounds (-686459 / 8000000) (-42903687 / 500000000) (Real.log (917771 / 1000000)) := by
  have h := reflection_log_1854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1855_neg : (6784571 / 1000000000) ≤ -Real.log (993238391559 / 1000000000000) ∧
    -Real.log (993238391559 / 1000000000000) ≤ (1696143 / 250000000) := by
  have h := checkLog_sound (w := (6761608441 / 1993238391559)) (n := 12)
    (lo := (6784571 / 1000000000)) (hi := (1696143 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993238391559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993238391559) = 1/(993238391559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1855 : Bounds (-1696143 / 250000000) (-6784571 / 1000000000) (Real.log (993238391559 / 1000000000000)) := by
  have h := reflection_log_1855_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
