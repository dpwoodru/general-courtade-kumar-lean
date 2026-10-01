import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3776_neg : (89432673 / 500000000) ≤ -Real.log (250000000000 / 298964926631) ∧
    -Real.log (250000000000 / 298964926631) ≤ (178865347 / 1000000000) := by
  have h := checkLog_sound (w := (48964926631 / 548964926631)) (n := 12)
    (lo := (89432673 / 500000000)) (hi := (178865347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298964926631 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298964926631 / 250000000000) = 1/(250000000000 / 298964926631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3776 : Bounds (89432673 / 500000000) (178865347 / 1000000000) (Real.log (298964926631 / 250000000000)) := by
  have h := reflection_log_3776_neg
  have he : Real.log (298964926631 / 250000000000) = -Real.log (250000000000 / 298964926631) := by
    rw [show ((298964926631 / 250000000000) : ℝ) = ((250000000000 / 298964926631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3777_neg : (178987189 / 500000000) ≤ -Real.log (125000000000 / 178803621339) ∧
    -Real.log (125000000000 / 178803621339) ≤ (357974379 / 1000000000) := by
  have h := checkLog_sound (w := (53803621339 / 303803621339)) (n := 12)
    (lo := (178987189 / 500000000)) (hi := (357974379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178803621339 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178803621339 / 125000000000) = 1/(125000000000 / 178803621339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3777 : Bounds (178987189 / 500000000) (357974379 / 1000000000) (Real.log (178803621339 / 125000000000)) := by
  have h := reflection_log_3777_neg
  have he : Real.log (178803621339 / 125000000000) = -Real.log (125000000000 / 178803621339) := by
    rw [show ((178803621339 / 125000000000) : ℝ) = ((125000000000 / 178803621339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3778_neg : (179090429 / 500000000) ≤ -Real.log (50000000000 / 71536217793) ∧
    -Real.log (50000000000 / 71536217793) ≤ (358180859 / 1000000000) := by
  have h := checkLog_sound (w := (21536217793 / 121536217793)) (n := 12)
    (lo := (179090429 / 500000000)) (hi := (358180859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71536217793 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71536217793 / 50000000000) = 1/(50000000000 / 71536217793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3778 : Bounds (179090429 / 500000000) (358180859 / 1000000000) (Real.log (71536217793 / 50000000000)) := by
  have h := reflection_log_3778_neg
  have he : Real.log (71536217793 / 50000000000) = -Real.log (50000000000 / 71536217793) := by
    rw [show ((71536217793 / 50000000000) : ℝ) = ((50000000000 / 71536217793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3779_neg : (163223681 / 1000000000) ≤ -Real.log (10000 / 11773) ∧
    -Real.log (10000 / 11773) ≤ (81611841 / 500000000) := by
  have h := checkLog_sound (w := (1773 / 21773)) (n := 12)
    (lo := (163223681 / 1000000000)) (hi := (81611841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11773 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11773 / 10000) = 1/(10000 / 11773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3779 : Bounds (163223681 / 1000000000) (81611841 / 500000000) (Real.log (11773 / 10000)) := by
  have h := reflection_log_3779_neg
  have he : Real.log (11773 / 10000) = -Real.log (10000 / 11773) := by
    rw [show ((11773 / 10000) : ℝ) = ((10000 / 11773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3780_neg : (12197729 / 62500000) ≤ -Real.log (8227 / 10000) ∧
    -Real.log (8227 / 10000) ≤ (39032733 / 200000000) := by
  have h := checkLog_sound (w := (1773 / 18227)) (n := 12)
    (lo := (12197729 / 62500000)) (hi := (39032733 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8227) = 1/(8227 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3780 : Bounds (-39032733 / 200000000) (-12197729 / 62500000) (Real.log (8227 / 10000)) := by
  have h := reflection_log_3780_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3781_neg : (44321 / 250000000) ≤ -Real.log (10000000 / 10001773) ∧
    -Real.log (10000000 / 10001773) ≤ (35457 / 200000000) := by
  have h := checkLog_sound (w := (1773 / 20001773)) (n := 12)
    (lo := (44321 / 250000000)) (hi := (35457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001773 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001773 / 10000000) = 1/(10000000 / 10001773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3781 : Bounds (44321 / 250000000) (35457 / 200000000) (Real.log (10001773 / 10000000)) := by
  have h := reflection_log_3781_neg
  have he : Real.log (10001773 / 10000000) = -Real.log (10000000 / 10001773) := by
    rw [show ((10001773 / 10000000) : ℝ) = ((10000000 / 10001773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3782_neg : (35463 / 200000000) ≤ -Real.log (9998227 / 10000000) ∧
    -Real.log (9998227 / 10000000) ≤ (44329 / 250000000) := by
  have h := checkLog_sound (w := (1773 / 19998227)) (n := 12)
    (lo := (35463 / 200000000)) (hi := (44329 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998227) = 1/(9998227 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3782 : Bounds (-44329 / 250000000) (-35463 / 200000000) (Real.log (9998227 / 10000000)) := by
  have h := reflection_log_3782_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3783_neg : (21319093 / 250000000) ≤ -Real.log (500000 / 544509) ∧
    -Real.log (500000 / 544509) ≤ (85276373 / 1000000000) := by
  have h := checkLog_sound (w := (44509 / 1044509)) (n := 12)
    (lo := (21319093 / 250000000)) (hi := (85276373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544509 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544509 / 500000) = 1/(500000 / 544509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3783 : Bounds (21319093 / 250000000) (85276373 / 1000000000) (Real.log (544509 / 500000)) := by
  have h := reflection_log_3783_neg
  have he : Real.log (544509 / 500000) = -Real.log (500000 / 544509) := by
    rw [show ((544509 / 500000) : ℝ) = ((500000 / 544509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3784_neg : (4661607 / 50000000) ≤ -Real.log (455491 / 500000) ∧
    -Real.log (455491 / 500000) ≤ (93232141 / 1000000000) := by
  have h := checkLog_sound (w := (44509 / 955491)) (n := 12)
    (lo := (4661607 / 50000000)) (hi := (93232141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455491) = 1/(455491 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3784 : Bounds (-93232141 / 1000000000) (-4661607 / 50000000) (Real.log (455491 / 500000)) := by
  have h := reflection_log_3784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3785_neg : (85485713 / 1000000000) ≤ -Real.log (500000 / 544623) ∧
    -Real.log (500000 / 544623) ≤ (42742857 / 500000000) := by
  have h := checkLog_sound (w := (44623 / 1044623)) (n := 12)
    (lo := (85485713 / 1000000000)) (hi := (42742857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544623 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544623 / 500000) = 1/(500000 / 544623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3785 : Bounds (85485713 / 1000000000) (42742857 / 500000000) (Real.log (544623 / 500000)) := by
  have h := reflection_log_3785_neg
  have he : Real.log (544623 / 500000) = -Real.log (500000 / 544623) := by
    rw [show ((544623 / 500000) : ℝ) = ((500000 / 544623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3786_neg : (93482451 / 1000000000) ≤ -Real.log (455377 / 500000) ∧
    -Real.log (455377 / 500000) ≤ (23370613 / 250000000) := by
  have h := checkLog_sound (w := (44623 / 955377)) (n := 12)
    (lo := (93482451 / 1000000000)) (hi := (23370613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455377) = 1/(455377 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3786 : Bounds (-23370613 / 250000000) (-93482451 / 1000000000) (Real.log (455377 / 500000)) := by
  have h := reflection_log_3786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3787_neg : (7996737 / 1000000000) ≤ -Real.log (248008787871 / 250000000000) ∧
    -Real.log (248008787871 / 250000000000) ≤ (3998369 / 500000000) := by
  have h := checkLog_sound (w := (1991212129 / 498008787871)) (n := 12)
    (lo := (7996737 / 1000000000)) (hi := (3998369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248008787871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248008787871) = 1/(248008787871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3787 : Bounds (-3998369 / 500000000) (-7996737 / 1000000000) (Real.log (248008787871 / 250000000000)) := by
  have h := reflection_log_3787_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3788_neg : (7955767 / 1000000000) ≤ -Real.log (248018948919 / 250000000000) ∧
    -Real.log (248018948919 / 250000000000) ≤ (994471 / 125000000) := by
  have h := checkLog_sound (w := (1981051081 / 498018948919)) (n := 12)
    (lo := (7955767 / 1000000000)) (hi := (994471 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248018948919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248018948919) = 1/(248018948919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3788 : Bounds (-994471 / 125000000) (-7955767 / 1000000000) (Real.log (248018948919 / 250000000000)) := by
  have h := reflection_log_3788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3789_neg : (178508513 / 1000000000) ≤ -Real.log (250000000000 / 298858265037) ∧
    -Real.log (250000000000 / 298858265037) ≤ (89254257 / 500000000) := by
  have h := checkLog_sound (w := (48858265037 / 548858265037)) (n := 12)
    (lo := (178508513 / 1000000000)) (hi := (89254257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298858265037 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298858265037 / 250000000000) = 1/(250000000000 / 298858265037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3789 : Bounds (178508513 / 1000000000) (89254257 / 500000000) (Real.log (298858265037 / 250000000000)) := by
  have h := reflection_log_3789_neg
  have he : Real.log (298858265037 / 250000000000) = -Real.log (250000000000 / 298858265037) := by
    rw [show ((298858265037 / 250000000000) : ℝ) = ((250000000000 / 298858265037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3790_neg : (44742041 / 250000000) ≤ -Real.log (500000000000 / 597991334653) ∧
    -Real.log (500000000000 / 597991334653) ≤ (35793633 / 200000000) := by
  have h := checkLog_sound (w := (97991334653 / 1097991334653)) (n := 12)
    (lo := (44742041 / 250000000)) (hi := (35793633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597991334653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597991334653 / 500000000000) = 1/(500000000000 / 597991334653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3790 : Bounds (44742041 / 250000000) (35793633 / 200000000) (Real.log (597991334653 / 500000000000)) := by
  have h := reflection_log_3790_neg
  have he : Real.log (597991334653 / 500000000000) = -Real.log (500000000000 / 597991334653) := by
    rw [show ((597991334653 / 500000000000) : ℝ) = ((500000000000 / 597991334653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3791_neg : (179090429 / 500000000) ≤ -Real.log (500000000000 / 715362177929) ∧
    -Real.log (500000000000 / 715362177929) ≤ (358180859 / 1000000000) := by
  have h := checkLog_sound (w := (215362177929 / 1215362177929)) (n := 12)
    (lo := (179090429 / 500000000)) (hi := (358180859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715362177929 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715362177929 / 500000000000) = 1/(500000000000 / 715362177929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3791 : Bounds (179090429 / 500000000) (358180859 / 1000000000) (Real.log (715362177929 / 500000000000)) := by
  have h := reflection_log_3791_neg
  have he : Real.log (715362177929 / 500000000000) = -Real.log (500000000000 / 715362177929) := by
    rw [show ((715362177929 / 500000000000) : ℝ) = ((500000000000 / 715362177929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3792_neg : (71677469 / 200000000) ≤ -Real.log (250000000000 / 357754953203) ∧
    -Real.log (250000000000 / 357754953203) ≤ (179193673 / 500000000) := by
  have h := checkLog_sound (w := (107754953203 / 607754953203)) (n := 12)
    (lo := (71677469 / 200000000)) (hi := (179193673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357754953203 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357754953203 / 250000000000) = 1/(250000000000 / 357754953203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3792 : Bounds (71677469 / 200000000) (179193673 / 500000000) (Real.log (357754953203 / 250000000000)) := by
  have h := reflection_log_3792_neg
  have he : Real.log (357754953203 / 250000000000) = -Real.log (250000000000 / 357754953203) := by
    rw [show ((357754953203 / 250000000000) : ℝ) = ((250000000000 / 357754953203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3793_neg : (163308617 / 1000000000) ≤ -Real.log (5000 / 5887) ∧
    -Real.log (5000 / 5887) ≤ (81654309 / 500000000) := by
  have h := checkLog_sound (w := (887 / 10887)) (n := 12)
    (lo := (163308617 / 1000000000)) (hi := (81654309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5887 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5887 / 5000) = 1/(5000 / 5887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3793 : Bounds (163308617 / 1000000000) (81654309 / 500000000) (Real.log (5887 / 5000)) := by
  have h := reflection_log_3793_neg
  have he : Real.log (5887 / 5000) = -Real.log (5000 / 5887) := by
    rw [show ((5887 / 5000) : ℝ) = ((5000 / 5887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3794_neg : (195285223 / 1000000000) ≤ -Real.log (4113 / 5000) ∧
    -Real.log (4113 / 5000) ≤ (24410653 / 125000000) := by
  have h := checkLog_sound (w := (887 / 9113)) (n := 12)
    (lo := (195285223 / 1000000000)) (hi := (24410653 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4113) = 1/(4113 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3794 : Bounds (-24410653 / 125000000) (-195285223 / 1000000000) (Real.log (4113 / 5000)) := by
  have h := reflection_log_3794_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3795_neg : (22173 / 125000000) ≤ -Real.log (5000000 / 5000887) ∧
    -Real.log (5000000 / 5000887) ≤ (35477 / 200000000) := by
  have h := checkLog_sound (w := (887 / 10000887)) (n := 12)
    (lo := (22173 / 125000000)) (hi := (35477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000887 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000887 / 5000000) = 1/(5000000 / 5000887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3795 : Bounds (22173 / 125000000) (35477 / 200000000) (Real.log (5000887 / 5000000)) := by
  have h := reflection_log_3795_neg
  have he : Real.log (5000887 / 5000000) = -Real.log (5000000 / 5000887) := by
    rw [show ((5000887 / 5000000) : ℝ) = ((5000000 / 5000887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3796_neg : (35483 / 200000000) ≤ -Real.log (4999113 / 5000000) ∧
    -Real.log (4999113 / 5000000) ≤ (22177 / 125000000) := by
  have h := checkLog_sound (w := (887 / 9999113)) (n := 12)
    (lo := (35483 / 200000000)) (hi := (22177 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999113) = 1/(4999113 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3796 : Bounds (-22177 / 125000000) (-35483 / 200000000) (Real.log (4999113 / 5000000)) := by
  have h := reflection_log_3796_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3797_neg : (42661601 / 500000000) ≤ -Real.log (1000000 / 1089069) ∧
    -Real.log (1000000 / 1089069) ≤ (85323203 / 1000000000) := by
  have h := checkLog_sound (w := (89069 / 2089069)) (n := 12)
    (lo := (42661601 / 500000000)) (hi := (85323203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089069 / 1000000) = 1/(1000000 / 1089069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3797 : Bounds (42661601 / 500000000) (85323203 / 1000000000) (Real.log (1089069 / 1000000)) := by
  have h := reflection_log_3797_neg
  have he : Real.log (1089069 / 1000000) = -Real.log (1000000 / 1089069) := by
    rw [show ((1089069 / 1000000) : ℝ) = ((1000000 / 1089069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3798_neg : (149261 / 1600000) ≤ -Real.log (910931 / 1000000) ∧
    -Real.log (910931 / 1000000) ≤ (46644063 / 500000000) := by
  have h := checkLog_sound (w := (89069 / 1910931)) (n := 12)
    (lo := (149261 / 1600000)) (hi := (46644063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910931) = 1/(910931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3798 : Bounds (-46644063 / 500000000) (-149261 / 1600000) (Real.log (910931 / 1000000)) := by
  have h := reflection_log_3798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3799_neg : (42766267 / 500000000) ≤ -Real.log (1000000 / 1089297) ∧
    -Real.log (1000000 / 1089297) ≤ (17106507 / 200000000) := by
  have h := checkLog_sound (w := (89297 / 2089297)) (n := 12)
    (lo := (42766267 / 500000000)) (hi := (17106507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089297 / 1000000) = 1/(1000000 / 1089297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3799 : Bounds (42766267 / 500000000) (17106507 / 200000000) (Real.log (1089297 / 1000000)) := by
  have h := reflection_log_3799_neg
  have he : Real.log (1089297 / 1000000) = -Real.log (1000000 / 1089297) := by
    rw [show ((1089297 / 1000000) : ℝ) = ((1000000 / 1089297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3800_neg : (1870769 / 20000000) ≤ -Real.log (910703 / 1000000) ∧
    -Real.log (910703 / 1000000) ≤ (93538451 / 1000000000) := by
  have h := checkLog_sound (w := (89297 / 1910703)) (n := 12)
    (lo := (1870769 / 20000000)) (hi := (93538451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910703) = 1/(910703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3800 : Bounds (-93538451 / 1000000000) (-1870769 / 20000000) (Real.log (910703 / 1000000)) := by
  have h := reflection_log_3800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3801_neg : (2001479 / 250000000) ≤ -Real.log (992026045791 / 1000000000000) ∧
    -Real.log (992026045791 / 1000000000000) ≤ (8005917 / 1000000000) := by
  have h := checkLog_sound (w := (7973954209 / 1992026045791)) (n := 12)
    (lo := (2001479 / 250000000)) (hi := (8005917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992026045791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992026045791) = 1/(992026045791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3801 : Bounds (-8005917 / 1000000000) (-2001479 / 250000000) (Real.log (992026045791 / 1000000000000)) := by
  have h := reflection_log_3801_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3802_neg : (3982461 / 500000000) ≤ -Real.log (992066713239 / 1000000000000) ∧
    -Real.log (992066713239 / 1000000000000) ≤ (7964923 / 1000000000) := by
  have h := checkLog_sound (w := (7933286761 / 1992066713239)) (n := 12)
    (lo := (3982461 / 500000000)) (hi := (7964923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992066713239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992066713239) = 1/(992066713239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3802 : Bounds (-7964923 / 1000000000) (-3982461 / 500000000) (Real.log (992066713239 / 1000000000000)) := by
  have h := reflection_log_3802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3803_neg : (1395401 / 7812500) ≤ -Real.log (20000000000 / 23911119503) ∧
    -Real.log (20000000000 / 23911119503) ≤ (178611329 / 1000000000) := by
  have h := checkLog_sound (w := (3911119503 / 43911119503)) (n := 12)
    (lo := (1395401 / 7812500)) (hi := (178611329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23911119503 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23911119503 / 20000000000) = 1/(20000000000 / 23911119503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3803 : Bounds (1395401 / 7812500) (178611329 / 1000000000) (Real.log (23911119503 / 20000000000)) := by
  have h := reflection_log_3803_neg
  have he : Real.log (23911119503 / 20000000000) = -Real.log (20000000000 / 23911119503) := by
    rw [show ((23911119503 / 20000000000) : ℝ) = ((20000000000 / 23911119503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3804_neg : (22383873 / 125000000) ≤ -Real.log (50000000000 / 59805282293) ∧
    -Real.log (50000000000 / 59805282293) ≤ (35814197 / 200000000) := by
  have h := checkLog_sound (w := (9805282293 / 109805282293)) (n := 12)
    (lo := (22383873 / 125000000)) (hi := (35814197 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59805282293 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59805282293 / 50000000000) = 1/(50000000000 / 59805282293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3804 : Bounds (22383873 / 125000000) (35814197 / 200000000) (Real.log (59805282293 / 50000000000)) := by
  have h := reflection_log_3804_neg
  have he : Real.log (59805282293 / 50000000000) = -Real.log (50000000000 / 59805282293) := by
    rw [show ((59805282293 / 50000000000) : ℝ) = ((50000000000 / 59805282293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3805_neg : (71677469 / 200000000) ≤ -Real.log (100000000000 / 143101981281) ∧
    -Real.log (100000000000 / 143101981281) ≤ (179193673 / 500000000) := by
  have h := checkLog_sound (w := (43101981281 / 243101981281)) (n := 12)
    (lo := (71677469 / 200000000)) (hi := (179193673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143101981281 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143101981281 / 100000000000) = 1/(100000000000 / 143101981281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3805 : Bounds (71677469 / 200000000) (179193673 / 500000000) (Real.log (143101981281 / 100000000000)) := by
  have h := reflection_log_3805_neg
  have he : Real.log (143101981281 / 100000000000) = -Real.log (100000000000 / 143101981281) := by
    rw [show ((143101981281 / 100000000000) : ℝ) = ((100000000000 / 143101981281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3806_neg : (4482423 / 12500000) ≤ -Real.log (1250000000 / 1789144177) ∧
    -Real.log (1250000000 / 1789144177) ≤ (358593841 / 1000000000) := by
  have h := checkLog_sound (w := (539144177 / 3039144177)) (n := 12)
    (lo := (4482423 / 12500000)) (hi := (358593841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1789144177 / 1250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1789144177 / 1250000000) = 1/(1250000000 / 1789144177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3806 : Bounds (4482423 / 12500000) (358593841 / 1000000000) (Real.log (1789144177 / 1250000000)) := by
  have h := reflection_log_3806_neg
  have he : Real.log (1789144177 / 1250000000) = -Real.log (1250000000 / 1789144177) := by
    rw [show ((1789144177 / 1250000000) : ℝ) = ((1250000000 / 1789144177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3807_neg : (81696773 / 500000000) ≤ -Real.log (400 / 471) ∧
    -Real.log (400 / 471) ≤ (163393547 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 871)) (n := 12)
    (lo := (81696773 / 500000000)) (hi := (163393547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471 / 400) = 1/(400 / 471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3807 : Bounds (81696773 / 500000000) (163393547 / 1000000000) (Real.log (471 / 400)) := by
  have h := reflection_log_3807_neg
  have he : Real.log (471 / 400) = -Real.log (400 / 471) := by
    rw [show ((471 / 400) : ℝ) = ((400 / 471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3808_neg : (48851699 / 250000000) ≤ -Real.log (329 / 400) ∧
    -Real.log (329 / 400) ≤ (195406797 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 729)) (n := 12)
    (lo := (48851699 / 250000000)) (hi := (195406797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 329) = 1/(329 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3808 : Bounds (-195406797 / 1000000000) (-48851699 / 250000000) (Real.log (329 / 400)) := by
  have h := reflection_log_3808_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3809_neg : (44371 / 250000000) ≤ -Real.log (400000 / 400071) ∧
    -Real.log (400000 / 400071) ≤ (35497 / 200000000) := by
  have h := checkLog_sound (w := (71 / 800071)) (n := 12)
    (lo := (44371 / 250000000)) (hi := (35497 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400071 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400071 / 400000) = 1/(400000 / 400071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3809 : Bounds (44371 / 250000000) (35497 / 200000000) (Real.log (400071 / 400000)) := by
  have h := reflection_log_3809_neg
  have he : Real.log (400071 / 400000) = -Real.log (400000 / 400071) := by
    rw [show ((400071 / 400000) : ℝ) = ((400000 / 400071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3810_neg : (35503 / 200000000) ≤ -Real.log (399929 / 400000) ∧
    -Real.log (399929 / 400000) ≤ (44379 / 250000000) := by
  have h := checkLog_sound (w := (71 / 799929)) (n := 12)
    (lo := (35503 / 200000000)) (hi := (44379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399929) = 1/(399929 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3810 : Bounds (-44379 / 250000000) (-35503 / 200000000) (Real.log (399929 / 400000)) := by
  have h := reflection_log_3810_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3811_neg : (10671139 / 125000000) ≤ -Real.log (1000000 / 1089119) ∧
    -Real.log (1000000 / 1089119) ≤ (85369113 / 1000000000) := by
  have h := checkLog_sound (w := (89119 / 2089119)) (n := 12)
    (lo := (10671139 / 125000000)) (hi := (85369113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089119 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089119 / 1000000) = 1/(1000000 / 1089119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3811 : Bounds (10671139 / 125000000) (85369113 / 1000000000) (Real.log (1089119 / 1000000)) := by
  have h := reflection_log_3811_neg
  have he : Real.log (1089119 / 1000000) = -Real.log (1000000 / 1089119) := by
    rw [show ((1089119 / 1000000) : ℝ) = ((1000000 / 1089119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3812_neg : (18668603 / 200000000) ≤ -Real.log (910881 / 1000000) ∧
    -Real.log (910881 / 1000000) ≤ (11667877 / 125000000) := by
  have h := checkLog_sound (w := (89119 / 1910881)) (n := 12)
    (lo := (18668603 / 200000000)) (hi := (11667877 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910881) = 1/(910881 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3812 : Bounds (-11667877 / 125000000) (-18668603 / 200000000) (Real.log (910881 / 1000000)) := by
  have h := reflection_log_3812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3813_neg : (10697419 / 125000000) ≤ -Real.log (250000 / 272337) ∧
    -Real.log (250000 / 272337) ≤ (85579353 / 1000000000) := by
  have h := checkLog_sound (w := (22337 / 522337)) (n := 12)
    (lo := (10697419 / 125000000)) (hi := (85579353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272337 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272337 / 250000) = 1/(250000 / 272337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3813 : Bounds (10697419 / 125000000) (85579353 / 1000000000) (Real.log (272337 / 250000)) := by
  have h := reflection_log_3813_neg
  have he : Real.log (272337 / 250000) = -Real.log (250000 / 272337) := by
    rw [show ((272337 / 250000) : ℝ) = ((250000 / 272337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3814_neg : (23398613 / 250000000) ≤ -Real.log (227663 / 250000) ∧
    -Real.log (227663 / 250000) ≤ (93594453 / 1000000000) := by
  have h := checkLog_sound (w := (22337 / 477663)) (n := 12)
    (lo := (23398613 / 250000000)) (hi := (93594453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227663) = 1/(227663 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3814 : Bounds (-93594453 / 1000000000) (-23398613 / 250000000) (Real.log (227663 / 250000)) := by
  have h := reflection_log_3814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3815_neg : (80151 / 10000000) ≤ -Real.log (62001058431 / 62500000000) ∧
    -Real.log (62001058431 / 62500000000) ≤ (8015101 / 1000000000) := by
  have h := checkLog_sound (w := (498941569 / 124501058431)) (n := 12)
    (lo := (80151 / 10000000)) (hi := (8015101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62001058431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62001058431) = 1/(62001058431 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3815 : Bounds (-8015101 / 1000000000) (-80151 / 10000000) (Real.log (62001058431 / 62500000000)) := by
  have h := reflection_log_3815_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3816_neg : (7973903 / 1000000000) ≤ -Real.log (992057803839 / 1000000000000) ∧
    -Real.log (992057803839 / 1000000000000) ≤ (498369 / 62500000) := by
  have h := checkLog_sound (w := (7942196161 / 1992057803839)) (n := 12)
    (lo := (7973903 / 1000000000)) (hi := (498369 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992057803839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992057803839) = 1/(992057803839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3816 : Bounds (-498369 / 62500000) (-7973903 / 1000000000) (Real.log (992057803839 / 1000000000000)) := by
  have h := reflection_log_3816_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3817_neg : (2792377 / 15625000) ≤ -Real.log (125000000000 / 149459561677) ∧
    -Real.log (125000000000 / 149459561677) ≤ (178712129 / 1000000000) := by
  have h := checkLog_sound (w := (24459561677 / 274459561677)) (n := 12)
    (lo := (2792377 / 15625000)) (hi := (178712129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149459561677 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149459561677 / 125000000000) = 1/(125000000000 / 149459561677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3817 : Bounds (2792377 / 15625000) (178712129 / 1000000000) (Real.log (149459561677 / 125000000000)) := by
  have h := reflection_log_3817_neg
  have he : Real.log (149459561677 / 125000000000) = -Real.log (125000000000 / 149459561677) := by
    rw [show ((149459561677 / 125000000000) : ℝ) = ((125000000000 / 149459561677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3818_neg : (44793451 / 250000000) ≤ -Real.log (500000000000 / 598114318093) ∧
    -Real.log (500000000000 / 598114318093) ≤ (35834761 / 200000000) := by
  have h := checkLog_sound (w := (98114318093 / 1098114318093)) (n := 12)
    (lo := (44793451 / 250000000)) (hi := (35834761 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598114318093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598114318093 / 500000000000) = 1/(500000000000 / 598114318093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3818 : Bounds (44793451 / 250000000) (35834761 / 200000000) (Real.log (598114318093 / 500000000000)) := by
  have h := reflection_log_3818_neg
  have he : Real.log (598114318093 / 500000000000) = -Real.log (500000000000 / 598114318093) := by
    rw [show ((598114318093 / 500000000000) : ℝ) = ((500000000000 / 598114318093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3819_neg : (4482423 / 12500000) ≤ -Real.log (500000000000 / 715657670799) ∧
    -Real.log (500000000000 / 715657670799) ≤ (358593841 / 1000000000) := by
  have h := checkLog_sound (w := (215657670799 / 1215657670799)) (n := 12)
    (lo := (4482423 / 12500000)) (hi := (358593841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715657670799 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715657670799 / 500000000000) = 1/(500000000000 / 715657670799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3819 : Bounds (4482423 / 12500000) (358593841 / 1000000000) (Real.log (715657670799 / 500000000000)) := by
  have h := reflection_log_3819_neg
  have he : Real.log (715657670799 / 500000000000) = -Real.log (500000000000 / 715657670799) := by
    rw [show ((715657670799 / 500000000000) : ℝ) = ((500000000000 / 715657670799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3820_neg : (358800343 / 1000000000) ≤ -Real.log (4000000000 / 5726443769) ∧
    -Real.log (4000000000 / 5726443769) ≤ (44850043 / 125000000) := by
  have h := checkLog_sound (w := (1726443769 / 9726443769)) (n := 12)
    (lo := (358800343 / 1000000000)) (hi := (44850043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5726443769 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5726443769 / 4000000000) = 1/(4000000000 / 5726443769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3820 : Bounds (358800343 / 1000000000) (44850043 / 125000000) (Real.log (5726443769 / 4000000000)) := by
  have h := reflection_log_3820_neg
  have he : Real.log (5726443769 / 4000000000) = -Real.log (4000000000 / 5726443769) := by
    rw [show ((5726443769 / 4000000000) : ℝ) = ((4000000000 / 5726443769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3821_neg : (40869617 / 250000000) ≤ -Real.log (625 / 736) ∧
    -Real.log (625 / 736) ≤ (163478469 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 1361)) (n := 12)
    (lo := (40869617 / 250000000)) (hi := (163478469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736 / 625) = 1/(625 / 736) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3821 : Bounds (40869617 / 250000000) (163478469 / 1000000000) (Real.log (736 / 625)) := by
  have h := reflection_log_3821_neg
  have he : Real.log (736 / 625) = -Real.log (625 / 736) := by
    rw [show ((736 / 625) : ℝ) = ((625 / 736) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3822_neg : (3055131 / 15625000) ≤ -Real.log (514 / 625) ∧
    -Real.log (514 / 625) ≤ (39105677 / 200000000) := by
  have h := checkLog_sound (w := (111 / 1139)) (n := 12)
    (lo := (3055131 / 15625000)) (hi := (39105677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 514) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 514) = 1/(514 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3822 : Bounds (-39105677 / 200000000) (-3055131 / 15625000) (Real.log (514 / 625)) := by
  have h := reflection_log_3822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3823_neg : (11099 / 62500000) ≤ -Real.log (625000 / 625111) ∧
    -Real.log (625000 / 625111) ≤ (35517 / 200000000) := by
  have h := checkLog_sound (w := (111 / 1250111)) (n := 12)
    (lo := (11099 / 62500000)) (hi := (35517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625111 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625111 / 625000) = 1/(625000 / 625111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3823 : Bounds (11099 / 62500000) (35517 / 200000000) (Real.log (625111 / 625000)) := by
  have h := reflection_log_3823_neg
  have he : Real.log (625111 / 625000) = -Real.log (625000 / 625111) := by
    rw [show ((625111 / 625000) : ℝ) = ((625000 / 625111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3824_neg : (35523 / 200000000) ≤ -Real.log (624889 / 625000) ∧
    -Real.log (624889 / 625000) ≤ (11101 / 62500000) := by
  have h := checkLog_sound (w := (111 / 1249889)) (n := 12)
    (lo := (35523 / 200000000)) (hi := (11101 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624889) = 1/(624889 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3824 : Bounds (-11101 / 62500000) (-35523 / 200000000) (Real.log (624889 / 625000)) := by
  have h := reflection_log_3824_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3825_neg : (42707969 / 500000000) ≤ -Real.log (100000 / 108917) ∧
    -Real.log (100000 / 108917) ≤ (85415939 / 1000000000) := by
  have h := checkLog_sound (w := (8917 / 208917)) (n := 12)
    (lo := (42707969 / 500000000)) (hi := (85415939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108917 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108917 / 100000) = 1/(100000 / 108917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3825 : Bounds (42707969 / 500000000) (85415939 / 1000000000) (Real.log (108917 / 100000)) := by
  have h := reflection_log_3825_neg
  have he : Real.log (108917 / 100000) = -Real.log (100000 / 108917) := by
    rw [show ((108917 / 100000) : ℝ) = ((100000 / 108917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3826_neg : (93399007 / 1000000000) ≤ -Real.log (91083 / 100000) ∧
    -Real.log (91083 / 100000) ≤ (2918719 / 31250000) := by
  have h := checkLog_sound (w := (8917 / 191083)) (n := 12)
    (lo := (93399007 / 1000000000)) (hi := (2918719 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 91083) = 1/(91083 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3826 : Bounds (-2918719 / 31250000) (-93399007 / 1000000000) (Real.log (91083 / 100000)) := by
  have h := reflection_log_3826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3827_neg : (10703271 / 125000000) ≤ -Real.log (1000000 / 1089399) ∧
    -Real.log (1000000 / 1089399) ≤ (85626169 / 1000000000) := by
  have h := checkLog_sound (w := (89399 / 2089399)) (n := 12)
    (lo := (10703271 / 125000000)) (hi := (85626169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089399 / 1000000) = 1/(1000000 / 1089399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3827 : Bounds (10703271 / 125000000) (85626169 / 1000000000) (Real.log (1089399 / 1000000)) := by
  have h := reflection_log_3827_neg
  have he : Real.log (1089399 / 1000000) = -Real.log (1000000 / 1089399) := by
    rw [show ((1089399 / 1000000) : ℝ) = ((1000000 / 1089399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3828_neg : (93650457 / 1000000000) ≤ -Real.log (910601 / 1000000) ∧
    -Real.log (910601 / 1000000) ≤ (46825229 / 500000000) := by
  have h := checkLog_sound (w := (89399 / 1910601)) (n := 12)
    (lo := (93650457 / 1000000000)) (hi := (46825229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910601) = 1/(910601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3828 : Bounds (-46825229 / 500000000) (-93650457 / 1000000000) (Real.log (910601 / 1000000)) := by
  have h := reflection_log_3828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3829_neg : (8024289 / 1000000000) ≤ -Real.log (992007818799 / 1000000000000) ∧
    -Real.log (992007818799 / 1000000000000) ≤ (802429 / 100000000) := by
  have h := checkLog_sound (w := (7992181201 / 1992007818799)) (n := 12)
    (lo := (8024289 / 1000000000)) (hi := (802429 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992007818799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992007818799) = 1/(992007818799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3829 : Bounds (-802429 / 100000000) (-8024289 / 1000000000) (Real.log (992007818799 / 1000000000000)) := by
  have h := reflection_log_3829_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3830_neg : (1995767 / 250000000) ≤ -Real.log (9920487111 / 10000000000) ∧
    -Real.log (9920487111 / 10000000000) ≤ (7983069 / 1000000000) := by
  have h := checkLog_sound (w := (79512889 / 19920487111)) (n := 12)
    (lo := (1995767 / 250000000)) (hi := (7983069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9920487111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9920487111) = 1/(9920487111 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3830 : Bounds (-7983069 / 1000000000) (-1995767 / 250000000) (Real.log (9920487111 / 10000000000)) := by
  have h := reflection_log_3830_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3831_neg : (35762989 / 200000000) ≤ -Real.log (500000000000 / 597899717839) ∧
    -Real.log (500000000000 / 597899717839) ≤ (89407473 / 500000000) := by
  have h := checkLog_sound (w := (97899717839 / 1097899717839)) (n := 12)
    (lo := (35762989 / 200000000)) (hi := (89407473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597899717839 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597899717839 / 500000000000) = 1/(500000000000 / 597899717839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3831 : Bounds (35762989 / 200000000) (89407473 / 500000000) (Real.log (597899717839 / 500000000000)) := by
  have h := reflection_log_3831_neg
  have he : Real.log (597899717839 / 500000000000) = -Real.log (500000000000 / 597899717839) := by
    rw [show ((597899717839 / 500000000000) : ℝ) = ((500000000000 / 597899717839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3832_neg : (1434213 / 8000000) ≤ -Real.log (250000000000 / 299087910073) ∧
    -Real.log (250000000000 / 299087910073) ≤ (89638313 / 500000000) := by
  have h := checkLog_sound (w := (49087910073 / 549087910073)) (n := 12)
    (lo := (1434213 / 8000000)) (hi := (89638313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299087910073 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299087910073 / 250000000000) = 1/(250000000000 / 299087910073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3832 : Bounds (1434213 / 8000000) (89638313 / 500000000) (Real.log (299087910073 / 250000000000)) := by
  have h := reflection_log_3832_neg
  have he : Real.log (299087910073 / 250000000000) = -Real.log (250000000000 / 299087910073) := by
    rw [show ((299087910073 / 250000000000) : ℝ) = ((250000000000 / 299087910073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3833_neg : (358800343 / 1000000000) ≤ -Real.log (125000000000 / 178951367781) ∧
    -Real.log (125000000000 / 178951367781) ≤ (44850043 / 125000000) := by
  have h := checkLog_sound (w := (53951367781 / 303951367781)) (n := 12)
    (lo := (358800343 / 1000000000)) (hi := (44850043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178951367781 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178951367781 / 125000000000) = 1/(125000000000 / 178951367781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3833 : Bounds (358800343 / 1000000000) (44850043 / 125000000) (Real.log (178951367781 / 125000000000)) := by
  have h := reflection_log_3833_neg
  have he : Real.log (178951367781 / 125000000000) = -Real.log (125000000000 / 178951367781) := by
    rw [show ((178951367781 / 125000000000) : ℝ) = ((125000000000 / 178951367781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3834_neg : (359006853 / 1000000000) ≤ -Real.log (500000000000 / 715953307393) ∧
    -Real.log (500000000000 / 715953307393) ≤ (179503427 / 500000000) := by
  have h := checkLog_sound (w := (215953307393 / 1215953307393)) (n := 12)
    (lo := (359006853 / 1000000000)) (hi := (179503427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715953307393 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715953307393 / 500000000000) = 1/(500000000000 / 715953307393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3834 : Bounds (359006853 / 1000000000) (179503427 / 500000000) (Real.log (715953307393 / 500000000000)) := by
  have h := reflection_log_3834_neg
  have he : Real.log (715953307393 / 500000000000) = -Real.log (500000000000 / 715953307393) := by
    rw [show ((715953307393 / 500000000000) : ℝ) = ((500000000000 / 715953307393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3835_neg : (163563383 / 1000000000) ≤ -Real.log (10000 / 11777) ∧
    -Real.log (10000 / 11777) ≤ (20445423 / 125000000) := by
  have h := checkLog_sound (w := (1777 / 21777)) (n := 12)
    (lo := (163563383 / 1000000000)) (hi := (20445423 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11777 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11777 / 10000) = 1/(10000 / 11777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3835 : Bounds (163563383 / 1000000000) (20445423 / 125000000) (Real.log (11777 / 10000)) := by
  have h := reflection_log_3835_neg
  have he : Real.log (11777 / 10000) = -Real.log (10000 / 11777) := by
    rw [show ((11777 / 10000) : ℝ) = ((10000 / 11777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3836_neg : (195649987 / 1000000000) ≤ -Real.log (8223 / 10000) ∧
    -Real.log (8223 / 10000) ≤ (48912497 / 250000000) := by
  have h := checkLog_sound (w := (1777 / 18223)) (n := 12)
    (lo := (195649987 / 1000000000)) (hi := (48912497 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8223) = 1/(8223 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3836 : Bounds (-48912497 / 250000000) (-195649987 / 1000000000) (Real.log (8223 / 10000)) := by
  have h := reflection_log_3836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3837_neg : (44421 / 250000000) ≤ -Real.log (10000000 / 10001777) ∧
    -Real.log (10000000 / 10001777) ≤ (35537 / 200000000) := by
  have h := checkLog_sound (w := (1777 / 20001777)) (n := 12)
    (lo := (44421 / 250000000)) (hi := (35537 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001777 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001777 / 10000000) = 1/(10000000 / 10001777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3837 : Bounds (44421 / 250000000) (35537 / 200000000) (Real.log (10001777 / 10000000)) := by
  have h := reflection_log_3837_neg
  have he : Real.log (10001777 / 10000000) = -Real.log (10000000 / 10001777) := by
    rw [show ((10001777 / 10000000) : ℝ) = ((10000000 / 10001777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3838_neg : (35543 / 200000000) ≤ -Real.log (9998223 / 10000000) ∧
    -Real.log (9998223 / 10000000) ≤ (44429 / 250000000) := by
  have h := checkLog_sound (w := (1777 / 19998223)) (n := 12)
    (lo := (35543 / 200000000)) (hi := (44429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998223) = 1/(9998223 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3838 : Bounds (-44429 / 250000000) (-35543 / 200000000) (Real.log (9998223 / 10000000)) := by
  have h := reflection_log_3838_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3839_neg : (85462761 / 1000000000) ≤ -Real.log (1000000 / 1089221) ∧
    -Real.log (1000000 / 1089221) ≤ (42731381 / 500000000) := by
  have h := checkLog_sound (w := (89221 / 2089221)) (n := 12)
    (lo := (85462761 / 1000000000)) (hi := (42731381 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089221 / 1000000) = 1/(1000000 / 1089221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3839 : Bounds (85462761 / 1000000000) (42731381 / 500000000) (Real.log (1089221 / 1000000)) := by
  have h := reflection_log_3839_neg
  have he : Real.log (1089221 / 1000000) = -Real.log (1000000 / 1089221) := by
    rw [show ((1089221 / 1000000) : ℝ) = ((1000000 / 1089221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
