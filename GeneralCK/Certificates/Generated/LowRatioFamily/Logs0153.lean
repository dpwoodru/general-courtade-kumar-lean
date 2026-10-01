import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9792_neg : (90242467 / 250000000) ≤ -Real.log (697 / 1000) ∧
    -Real.log (697 / 1000) ≤ (360969869 / 1000000000) := by
  have h := checkLog_sound (w := (303 / 1697)) (n := 12)
    (lo := (90242467 / 250000000)) (hi := (360969869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 697) = 1/(697 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9792 : Bounds (-360969869 / 1000000000) (-90242467 / 250000000) (Real.log (697 / 1000)) := by
  have h := reflection_log_9792_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9793_neg : (151477 / 500000000) ≤ -Real.log (1000000 / 1000303) ∧
    -Real.log (1000000 / 1000303) ≤ (60591 / 200000000) := by
  have h := checkLog_sound (w := (303 / 2000303)) (n := 12)
    (lo := (151477 / 500000000)) (hi := (60591 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000303 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000303 / 1000000) = 1/(1000000 / 1000303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9793 : Bounds (151477 / 500000000) (60591 / 200000000) (Real.log (1000303 / 1000000)) := by
  have h := reflection_log_9793_neg
  have he : Real.log (1000303 / 1000000) = -Real.log (1000000 / 1000303) := by
    rw [show ((1000303 / 1000000) : ℝ) = ((1000000 / 1000303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9794_neg : (60609 / 200000000) ≤ -Real.log (999697 / 1000000) ∧
    -Real.log (999697 / 1000000) ≤ (151523 / 500000000) := by
  have h := checkLog_sound (w := (303 / 1999697)) (n := 12)
    (lo := (60609 / 200000000)) (hi := (151523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999697) = 1/(999697 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9794 : Bounds (-151523 / 500000000) (-60609 / 200000000) (Real.log (999697 / 1000000)) := by
  have h := reflection_log_9794_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9795_neg : (14271757 / 100000000) ≤ -Real.log (250000 / 288351) ∧
    -Real.log (250000 / 288351) ≤ (142717571 / 1000000000) := by
  have h := checkLog_sound (w := (38351 / 538351)) (n := 12)
    (lo := (14271757 / 100000000)) (hi := (142717571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288351 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288351 / 250000) = 1/(250000 / 288351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9795 : Bounds (14271757 / 100000000) (142717571 / 1000000000) (Real.log (288351 / 250000)) := by
  have h := reflection_log_9795_neg
  have he : Real.log (288351 / 250000) = -Real.log (250000 / 288351) := by
    rw [show ((288351 / 250000) : ℝ) = ((250000 / 288351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9796_neg : (6661267 / 40000000) ≤ -Real.log (211649 / 250000) ∧
    -Real.log (211649 / 250000) ≤ (41632919 / 250000000) := by
  have h := checkLog_sound (w := (38351 / 461649)) (n := 12)
    (lo := (6661267 / 40000000)) (hi := (41632919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 211649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 211649) = 1/(211649 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9796 : Bounds (-41632919 / 250000000) (-6661267 / 40000000) (Real.log (211649 / 250000)) := by
  have h := reflection_log_9796_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9797_neg : (71715861 / 500000000) ≤ -Real.log (250000 / 288557) ∧
    -Real.log (250000 / 288557) ≤ (143431723 / 1000000000) := by
  have h := checkLog_sound (w := (38557 / 538557)) (n := 12)
    (lo := (71715861 / 500000000)) (hi := (143431723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288557 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288557 / 250000) = 1/(250000 / 288557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9797 : Bounds (71715861 / 500000000) (143431723 / 1000000000) (Real.log (288557 / 250000)) := by
  have h := reflection_log_9797_neg
  have he : Real.log (288557 / 250000) = -Real.log (250000 / 288557) := by
    rw [show ((288557 / 250000) : ℝ) = ((250000 / 288557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9798_neg : (167505459 / 1000000000) ≤ -Real.log (211443 / 250000) ∧
    -Real.log (211443 / 250000) ≤ (8375273 / 50000000) := by
  have h := checkLog_sound (w := (38557 / 461443)) (n := 12)
    (lo := (167505459 / 1000000000)) (hi := (8375273 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 211443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 211443) = 1/(211443 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9798 : Bounds (-8375273 / 50000000) (-167505459 / 1000000000) (Real.log (211443 / 250000)) := by
  have h := reflection_log_9798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9799_neg : (24073737 / 1000000000) ≤ -Real.log (61013357751 / 62500000000) ∧
    -Real.log (61013357751 / 62500000000) ≤ (12036869 / 500000000) := by
  have h := checkLog_sound (w := (1486642249 / 123513357751)) (n := 12)
    (lo := (24073737 / 1000000000)) (hi := (12036869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61013357751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61013357751) = 1/(61013357751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9799 : Bounds (-12036869 / 500000000) (-24073737 / 1000000000) (Real.log (61013357751 / 62500000000)) := by
  have h := reflection_log_9799_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9800_neg : (4762821 / 200000000) ≤ -Real.log (61029200799 / 62500000000) ∧
    -Real.log (61029200799 / 62500000000) ≤ (11907053 / 500000000) := by
  have h := checkLog_sound (w := (1470799201 / 123529200799)) (n := 12)
    (lo := (4762821 / 200000000)) (hi := (11907053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61029200799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61029200799) = 1/(61029200799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9800 : Bounds (-11907053 / 500000000) (-4762821 / 200000000) (Real.log (61029200799 / 62500000000)) := by
  have h := reflection_log_9800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9801_neg : (61849849 / 200000000) ≤ -Real.log (50000000000 / 68120095063) ∧
    -Real.log (50000000000 / 68120095063) ≤ (154624623 / 500000000) := by
  have h := checkLog_sound (w := (18120095063 / 118120095063)) (n := 12)
    (lo := (61849849 / 200000000)) (hi := (154624623 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68120095063 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68120095063 / 50000000000) = 1/(50000000000 / 68120095063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9801 : Bounds (61849849 / 200000000) (154624623 / 500000000) (Real.log (68120095063 / 50000000000)) := by
  have h := reflection_log_9801_neg
  have he : Real.log (68120095063 / 50000000000) = -Real.log (50000000000 / 68120095063) := by
    rw [show ((68120095063 / 50000000000) : ℝ) = ((50000000000 / 68120095063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9802_neg : (310937181 / 1000000000) ≤ -Real.log (100000000000 / 136470348983) ∧
    -Real.log (100000000000 / 136470348983) ≤ (155468591 / 500000000) := by
  have h := checkLog_sound (w := (36470348983 / 236470348983)) (n := 12)
    (lo := (310937181 / 1000000000)) (hi := (155468591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136470348983 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136470348983 / 100000000000) = 1/(100000000000 / 136470348983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9802 : Bounds (310937181 / 1000000000) (155468591 / 500000000) (Real.log (136470348983 / 100000000000)) := by
  have h := reflection_log_9802_neg
  have he : Real.log (136470348983 / 100000000000) = -Real.log (100000000000 / 136470348983) := by
    rw [show ((136470348983 / 100000000000) : ℝ) = ((100000000000 / 136470348983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9803_neg : (15585943 / 25000000) ≤ -Real.log (250000000000 / 466332378223) ∧
    -Real.log (250000000000 / 466332378223) ≤ (623437721 / 1000000000) := by
  have h := checkLog_sound (w := (216332378223 / 716332378223)) (n := 12)
    (lo := (15585943 / 25000000)) (hi := (623437721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((466332378223 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(466332378223 / 250000000000) = 1/(250000000000 / 466332378223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9803 : Bounds (15585943 / 25000000) (623437721 / 1000000000) (Real.log (466332378223 / 250000000000)) := by
  have h := reflection_log_9803_neg
  have he : Real.log (466332378223 / 250000000000) = -Real.log (250000000000 / 466332378223) := by
    rw [show ((466332378223 / 250000000000) : ℝ) = ((250000000000 / 466332378223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9804_neg : (312819583 / 500000000) ≤ -Real.log (125000000000 / 233680057389) ∧
    -Real.log (125000000000 / 233680057389) ≤ (625639167 / 1000000000) := by
  have h := checkLog_sound (w := (108680057389 / 358680057389)) (n := 12)
    (lo := (312819583 / 500000000)) (hi := (625639167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233680057389 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233680057389 / 125000000000) = 1/(125000000000 / 233680057389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9804 : Bounds (312819583 / 500000000) (625639167 / 1000000000) (Real.log (233680057389 / 125000000000)) := by
  have h := reflection_log_9804_neg
  have he : Real.log (233680057389 / 125000000000) = -Real.log (125000000000 / 233680057389) := by
    rw [show ((233680057389 / 125000000000) : ℝ) = ((125000000000 / 233680057389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9805_neg : (265436463 / 1000000000) ≤ -Real.log (125 / 163) ∧
    -Real.log (125 / 163) ≤ (16589779 / 62500000) := by
  have h := checkLog_sound (w := (19 / 144)) (n := 12)
    (lo := (265436463 / 1000000000)) (hi := (16589779 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163 / 125) = 1/(125 / 163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9805 : Bounds (265436463 / 1000000000) (16589779 / 62500000) (Real.log (163 / 125)) := by
  have h := reflection_log_9805_neg
  have he : Real.log (163 / 125) = -Real.log (125 / 163) := by
    rw [show ((163 / 125) : ℝ) = ((125 / 163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9806_neg : (181202809 / 500000000) ≤ -Real.log (87 / 125) ∧
    -Real.log (87 / 125) ≤ (362405619 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 106)) (n := 12)
    (lo := (181202809 / 500000000)) (hi := (362405619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 87) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 87) = 1/(87 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9806 : Bounds (-362405619 / 1000000000) (-181202809 / 500000000) (Real.log (87 / 125)) := by
  have h := reflection_log_9806_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9807_neg : (303953 / 1000000000) ≤ -Real.log (62500 / 62519) ∧
    -Real.log (62500 / 62519) ≤ (151977 / 500000000) := by
  have h := checkLog_sound (w := (19 / 125019)) (n := 12)
    (lo := (303953 / 1000000000)) (hi := (151977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62519 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62519 / 62500) = 1/(62500 / 62519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9807 : Bounds (303953 / 1000000000) (151977 / 500000000) (Real.log (62519 / 62500)) := by
  have h := reflection_log_9807_neg
  have he : Real.log (62519 / 62500) = -Real.log (62500 / 62519) := by
    rw [show ((62519 / 62500) : ℝ) = ((62500 / 62519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9808_neg : (152023 / 500000000) ≤ -Real.log (62481 / 62500) ∧
    -Real.log (62481 / 62500) ≤ (304047 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 124981)) (n := 12)
    (lo := (152023 / 500000000)) (hi := (304047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62481) = 1/(62481 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9808 : Bounds (-304047 / 1000000000) (-152023 / 500000000) (Real.log (62481 / 62500)) := by
  have h := reflection_log_9808_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9809_neg : (143172641 / 1000000000) ≤ -Real.log (1000000 / 1153929) ∧
    -Real.log (1000000 / 1153929) ≤ (71586321 / 500000000) := by
  have h := checkLog_sound (w := (153929 / 2153929)) (n := 12)
    (lo := (143172641 / 1000000000)) (hi := (71586321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1153929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1153929 / 1000000) = 1/(1000000 / 1153929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9809 : Bounds (143172641 / 1000000000) (71586321 / 500000000) (Real.log (1153929 / 1000000)) := by
  have h := reflection_log_9809_neg
  have he : Real.log (1153929 / 1000000) = -Real.log (1000000 / 1153929) := by
    rw [show ((1153929 / 1000000) : ℝ) = ((1000000 / 1153929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9810_neg : (83575999 / 500000000) ≤ -Real.log (846071 / 1000000) ∧
    -Real.log (846071 / 1000000) ≤ (167151999 / 1000000000) := by
  have h := checkLog_sound (w := (153929 / 1846071)) (n := 12)
    (lo := (83575999 / 500000000)) (hi := (167151999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 846071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 846071) = 1/(846071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9810 : Bounds (-167151999 / 1000000000) (-83575999 / 500000000) (Real.log (846071 / 1000000)) := by
  have h := reflection_log_9810_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9811_neg : (71943667 / 500000000) ≤ -Real.log (500000 / 577377) ∧
    -Real.log (500000 / 577377) ≤ (28777467 / 200000000) := by
  have h := checkLog_sound (w := (77377 / 1077377)) (n := 12)
    (lo := (71943667 / 500000000)) (hi := (28777467 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577377 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(577377 / 500000) = 1/(500000 / 577377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9811 : Bounds (71943667 / 500000000) (28777467 / 200000000) (Real.log (577377 / 500000)) := by
  have h := reflection_log_9811_neg
  have he : Real.log (577377 / 500000) = -Real.log (500000 / 577377) := by
    rw [show ((577377 / 500000) : ℝ) = ((500000 / 577377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9812_neg : (168127569 / 1000000000) ≤ -Real.log (422623 / 500000) ∧
    -Real.log (422623 / 500000) ≤ (16812757 / 100000000) := by
  have h := checkLog_sound (w := (77377 / 922623)) (n := 12)
    (lo := (168127569 / 1000000000)) (hi := (16812757 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 422623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 422623) = 1/(422623 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9812 : Bounds (-16812757 / 100000000) (-168127569 / 1000000000) (Real.log (422623 / 500000)) := by
  have h := reflection_log_9812_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9813_neg : (4848047 / 200000000) ≤ -Real.log (244012799871 / 250000000000) ∧
    -Real.log (244012799871 / 250000000000) ≤ (6060059 / 250000000) := by
  have h := checkLog_sound (w := (5987200129 / 494012799871)) (n := 12)
    (lo := (4848047 / 200000000)) (hi := (6060059 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244012799871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244012799871) = 1/(244012799871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9813 : Bounds (-6060059 / 250000000) (-4848047 / 200000000) (Real.log (244012799871 / 250000000000)) := by
  have h := reflection_log_9813_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9814_neg : (23979357 / 1000000000) ≤ -Real.log (976305862959 / 1000000000000) ∧
    -Real.log (976305862959 / 1000000000000) ≤ (11989679 / 500000000) := by
  have h := checkLog_sound (w := (23694137041 / 1976305862959)) (n := 12)
    (lo := (23979357 / 1000000000)) (hi := (11989679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976305862959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976305862959) = 1/(976305862959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9814 : Bounds (-11989679 / 500000000) (-23979357 / 1000000000) (Real.log (976305862959 / 1000000000000)) := by
  have h := reflection_log_9814_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9815_neg : (310324639 / 1000000000) ≤ -Real.log (125000000000 / 170483475973) ∧
    -Real.log (125000000000 / 170483475973) ≤ (1939529 / 6250000) := by
  have h := checkLog_sound (w := (45483475973 / 295483475973)) (n := 12)
    (lo := (310324639 / 1000000000)) (hi := (1939529 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170483475973 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170483475973 / 125000000000) = 1/(125000000000 / 170483475973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9815 : Bounds (310324639 / 1000000000) (1939529 / 6250000) (Real.log (170483475973 / 125000000000)) := by
  have h := reflection_log_9815_neg
  have he : Real.log (170483475973 / 125000000000) = -Real.log (125000000000 / 170483475973) := by
    rw [show ((170483475973 / 125000000000) : ℝ) = ((125000000000 / 170483475973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9816_neg : (39001863 / 125000000) ≤ -Real.log (250000000000 / 341543763591) ∧
    -Real.log (250000000000 / 341543763591) ≤ (62402981 / 200000000) := by
  have h := checkLog_sound (w := (91543763591 / 591543763591)) (n := 12)
    (lo := (39001863 / 125000000)) (hi := (62402981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341543763591 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341543763591 / 250000000000) = 1/(250000000000 / 341543763591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9816 : Bounds (39001863 / 125000000) (62402981 / 200000000) (Real.log (341543763591 / 250000000000)) := by
  have h := reflection_log_9816_neg
  have he : Real.log (341543763591 / 250000000000) = -Real.log (250000000000 / 341543763591) := by
    rw [show ((341543763591 / 250000000000) : ℝ) = ((250000000000 / 341543763591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9817_neg : (312819583 / 500000000) ≤ -Real.log (100000000000 / 186944045911) ∧
    -Real.log (100000000000 / 186944045911) ≤ (625639167 / 1000000000) := by
  have h := checkLog_sound (w := (86944045911 / 286944045911)) (n := 12)
    (lo := (312819583 / 500000000)) (hi := (625639167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186944045911 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186944045911 / 100000000000) = 1/(100000000000 / 186944045911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9817 : Bounds (312819583 / 500000000) (625639167 / 1000000000) (Real.log (186944045911 / 100000000000)) := by
  have h := reflection_log_9817_neg
  have he : Real.log (186944045911 / 100000000000) = -Real.log (100000000000 / 186944045911) := by
    rw [show ((186944045911 / 100000000000) : ℝ) = ((100000000000 / 186944045911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9818_neg : (313921041 / 500000000) ≤ -Real.log (125000000000 / 234195402299) ∧
    -Real.log (125000000000 / 234195402299) ≤ (627842083 / 1000000000) := by
  have h := checkLog_sound (w := (109195402299 / 359195402299)) (n := 12)
    (lo := (313921041 / 500000000)) (hi := (627842083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234195402299 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234195402299 / 125000000000) = 1/(125000000000 / 234195402299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9818 : Bounds (313921041 / 500000000) (627842083 / 1000000000) (Real.log (234195402299 / 125000000000)) := by
  have h := reflection_log_9818_neg
  have he : Real.log (234195402299 / 125000000000) = -Real.log (125000000000 / 234195402299) := by
    rw [show ((234195402299 / 125000000000) : ℝ) = ((125000000000 / 234195402299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9819_neg : (1663769 / 6250000) ≤ -Real.log (200 / 261) ∧
    -Real.log (200 / 261) ≤ (266203041 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 461)) (n := 12)
    (lo := (1663769 / 6250000)) (hi := (266203041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(261 / 200) = 1/(200 / 261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9819 : Bounds (1663769 / 6250000) (266203041 / 1000000000) (Real.log (261 / 200)) := by
  have h := reflection_log_9819_neg
  have he : Real.log (261 / 200) = -Real.log (200 / 261) := by
    rw [show ((261 / 200) : ℝ) = ((200 / 261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9820_neg : (363843433 / 1000000000) ≤ -Real.log (139 / 200) ∧
    -Real.log (139 / 200) ≤ (181921717 / 500000000) := by
  have h := checkLog_sound (w := (61 / 339)) (n := 12)
    (lo := (363843433 / 1000000000)) (hi := (181921717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 139) = 1/(139 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9820 : Bounds (-181921717 / 500000000) (-363843433 / 1000000000) (Real.log (139 / 200)) := by
  have h := reflection_log_9820_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9821_neg : (304953 / 1000000000) ≤ -Real.log (200000 / 200061) ∧
    -Real.log (200000 / 200061) ≤ (152477 / 500000000) := by
  have h := checkLog_sound (w := (61 / 400061)) (n := 12)
    (lo := (304953 / 1000000000)) (hi := (152477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200061 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200061 / 200000) = 1/(200000 / 200061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9821 : Bounds (304953 / 1000000000) (152477 / 500000000) (Real.log (200061 / 200000)) := by
  have h := reflection_log_9821_neg
  have he : Real.log (200061 / 200000) = -Real.log (200000 / 200061) := by
    rw [show ((200061 / 200000) : ℝ) = ((200000 / 200061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9822_neg : (152523 / 500000000) ≤ -Real.log (199939 / 200000) ∧
    -Real.log (199939 / 200000) ≤ (305047 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 399939)) (n := 12)
    (lo := (152523 / 500000000)) (hi := (305047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199939) = 1/(199939 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9822 : Bounds (-305047 / 1000000000) (-152523 / 500000000) (Real.log (199939 / 200000)) := by
  have h := reflection_log_9822_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9823_neg : (143628371 / 1000000000) ≤ -Real.log (200000 / 230891) ∧
    -Real.log (200000 / 230891) ≤ (35907093 / 250000000) := by
  have h := checkLog_sound (w := (30891 / 430891)) (n := 12)
    (lo := (143628371 / 1000000000)) (hi := (35907093 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230891 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(230891 / 200000) = 1/(200000 / 230891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9823 : Bounds (143628371 / 1000000000) (35907093 / 250000000) (Real.log (230891 / 200000)) := by
  have h := reflection_log_9823_neg
  have he : Real.log (230891 / 200000) = -Real.log (200000 / 230891) := by
    rw [show ((230891 / 200000) : ℝ) = ((200000 / 230891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9824_neg : (167773889 / 1000000000) ≤ -Real.log (169109 / 200000) ∧
    -Real.log (169109 / 200000) ≤ (16777389 / 100000000) := by
  have h := checkLog_sound (w := (30891 / 369109)) (n := 12)
    (lo := (167773889 / 1000000000)) (hi := (16777389 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 169109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 169109) = 1/(169109 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9824 : Bounds (-16777389 / 100000000) (-167773889 / 1000000000) (Real.log (169109 / 200000)) := by
  have h := reflection_log_9824_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9825_neg : (36085901 / 250000000) ≤ -Real.log (1000000 / 1155281) ∧
    -Real.log (1000000 / 1155281) ≤ (28868721 / 200000000) := by
  have h := checkLog_sound (w := (155281 / 2155281)) (n := 12)
    (lo := (36085901 / 250000000)) (hi := (28868721 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1155281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1155281 / 1000000) = 1/(1000000 / 1155281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9825 : Bounds (36085901 / 250000000) (28868721 / 200000000) (Real.log (1155281 / 1000000)) := by
  have h := reflection_log_9825_neg
  have he : Real.log (1155281 / 1000000) = -Real.log (1000000 / 1155281) := by
    rw [show ((1155281 / 1000000) : ℝ) = ((1000000 / 1155281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9826_neg : (168751251 / 1000000000) ≤ -Real.log (844719 / 1000000) ∧
    -Real.log (844719 / 1000000) ≤ (42187813 / 250000000) := by
  have h := checkLog_sound (w := (155281 / 1844719)) (n := 12)
    (lo := (168751251 / 1000000000)) (hi := (42187813 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 844719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 844719) = 1/(844719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9826 : Bounds (-42187813 / 250000000) (-168751251 / 1000000000) (Real.log (844719 / 1000000)) := by
  have h := reflection_log_9826_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9827_neg : (12203823 / 500000000) ≤ -Real.log (975887811039 / 1000000000000) ∧
    -Real.log (975887811039 / 1000000000000) ≤ (24407647 / 1000000000) := by
  have h := checkLog_sound (w := (24112188961 / 1975887811039)) (n := 12)
    (lo := (12203823 / 500000000)) (hi := (24407647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975887811039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975887811039) = 1/(975887811039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9827 : Bounds (-24407647 / 1000000000) (-12203823 / 500000000) (Real.log (975887811039 / 1000000000000)) := by
  have h := reflection_log_9827_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9828_neg : (24145517 / 1000000000) ≤ -Real.log (39045746119 / 40000000000) ∧
    -Real.log (39045746119 / 40000000000) ≤ (12072759 / 500000000) := by
  have h := checkLog_sound (w := (954253881 / 79045746119)) (n := 12)
    (lo := (24145517 / 1000000000)) (hi := (12072759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39045746119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39045746119) = 1/(39045746119 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9828 : Bounds (-12072759 / 500000000) (-24145517 / 1000000000) (Real.log (39045746119 / 40000000000)) := by
  have h := reflection_log_9828_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9829_neg : (15570113 / 50000000) ≤ -Real.log (12500000000 / 17066729151) ∧
    -Real.log (12500000000 / 17066729151) ≤ (311402261 / 1000000000) := by
  have h := checkLog_sound (w := (4566729151 / 29566729151)) (n := 12)
    (lo := (15570113 / 50000000)) (hi := (311402261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17066729151 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17066729151 / 12500000000) = 1/(12500000000 / 17066729151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9829 : Bounds (15570113 / 50000000) (311402261 / 1000000000) (Real.log (17066729151 / 12500000000)) := by
  have h := reflection_log_9829_neg
  have he : Real.log (17066729151 / 12500000000) = -Real.log (12500000000 / 17066729151) := by
    rw [show ((17066729151 / 12500000000) : ℝ) = ((12500000000 / 17066729151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9830_neg : (62618971 / 200000000) ≤ -Real.log (500000000000 / 683825627221) ∧
    -Real.log (500000000000 / 683825627221) ≤ (39136857 / 125000000) := by
  have h := checkLog_sound (w := (183825627221 / 1183825627221)) (n := 12)
    (lo := (62618971 / 200000000)) (hi := (39136857 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683825627221 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683825627221 / 500000000000) = 1/(500000000000 / 683825627221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9830 : Bounds (62618971 / 200000000) (39136857 / 125000000) (Real.log (683825627221 / 500000000000)) := by
  have h := reflection_log_9830_neg
  have he : Real.log (683825627221 / 500000000000) = -Real.log (500000000000 / 683825627221) := by
    rw [show ((683825627221 / 500000000000) : ℝ) = ((500000000000 / 683825627221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9831_neg : (313921041 / 500000000) ≤ -Real.log (100000000000 / 187356321839) ∧
    -Real.log (100000000000 / 187356321839) ≤ (627842083 / 1000000000) := by
  have h := checkLog_sound (w := (87356321839 / 287356321839)) (n := 12)
    (lo := (313921041 / 500000000)) (hi := (627842083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187356321839 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187356321839 / 100000000000) = 1/(100000000000 / 187356321839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9831 : Bounds (313921041 / 500000000) (627842083 / 1000000000) (Real.log (187356321839 / 100000000000)) := by
  have h := reflection_log_9831_neg
  have he : Real.log (187356321839 / 100000000000) = -Real.log (100000000000 / 187356321839) := by
    rw [show ((187356321839 / 100000000000) : ℝ) = ((100000000000 / 187356321839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9832_neg : (315023237 / 500000000) ≤ -Real.log (15625000000 / 29339028777) ∧
    -Real.log (15625000000 / 29339028777) ≤ (25201859 / 40000000) := by
  have h := checkLog_sound (w := (13714028777 / 44964028777)) (n := 12)
    (lo := (315023237 / 500000000)) (hi := (25201859 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29339028777 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29339028777 / 15625000000) = 1/(15625000000 / 29339028777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9832 : Bounds (315023237 / 500000000) (25201859 / 40000000) (Real.log (29339028777 / 15625000000)) := by
  have h := reflection_log_9832_neg
  have he : Real.log (29339028777 / 15625000000) = -Real.log (15625000000 / 29339028777) := by
    rw [show ((29339028777 / 15625000000) : ℝ) = ((15625000000 / 29339028777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9833_neg : (26696903 / 100000000) ≤ -Real.log (500 / 653) ∧
    -Real.log (500 / 653) ≤ (266969031 / 1000000000) := by
  have h := checkLog_sound (w := (153 / 1153)) (n := 12)
    (lo := (26696903 / 100000000)) (hi := (266969031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((653 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(653 / 500) = 1/(500 / 653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9833 : Bounds (26696903 / 100000000) (266969031 / 1000000000) (Real.log (653 / 500)) := by
  have h := reflection_log_9833_neg
  have he : Real.log (653 / 500) = -Real.log (500 / 653) := by
    rw [show ((653 / 500) : ℝ) = ((500 / 653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9834_neg : (182641659 / 500000000) ≤ -Real.log (347 / 500) ∧
    -Real.log (347 / 500) ≤ (365283319 / 1000000000) := by
  have h := checkLog_sound (w := (153 / 847)) (n := 12)
    (lo := (182641659 / 500000000)) (hi := (365283319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 347) = 1/(347 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9834 : Bounds (-365283319 / 1000000000) (-182641659 / 500000000) (Real.log (347 / 500)) := by
  have h := reflection_log_9834_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9835_neg : (305953 / 1000000000) ≤ -Real.log (500000 / 500153) ∧
    -Real.log (500000 / 500153) ≤ (152977 / 500000000) := by
  have h := checkLog_sound (w := (153 / 1000153)) (n := 12)
    (lo := (305953 / 1000000000)) (hi := (152977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500153 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500153 / 500000) = 1/(500000 / 500153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9835 : Bounds (305953 / 1000000000) (152977 / 500000000) (Real.log (500153 / 500000)) := by
  have h := reflection_log_9835_neg
  have he : Real.log (500153 / 500000) = -Real.log (500000 / 500153) := by
    rw [show ((500153 / 500000) : ℝ) = ((500000 / 500153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9836_neg : (153023 / 500000000) ≤ -Real.log (499847 / 500000) ∧
    -Real.log (499847 / 500000) ≤ (306047 / 1000000000) := by
  have h := checkLog_sound (w := (153 / 999847)) (n := 12)
    (lo := (153023 / 500000000)) (hi := (306047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499847) = 1/(499847 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9836 : Bounds (-306047 / 1000000000) (-153023 / 500000000) (Real.log (499847 / 500000)) := by
  have h := reflection_log_9836_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9837_neg : (144083027 / 1000000000) ≤ -Real.log (50000 / 57749) ∧
    -Real.log (50000 / 57749) ≤ (36020757 / 250000000) := by
  have h := checkLog_sound (w := (7749 / 107749)) (n := 12)
    (lo := (144083027 / 1000000000)) (hi := (36020757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57749 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57749 / 50000) = 1/(50000 / 57749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9837 : Bounds (144083027 / 1000000000) (36020757 / 250000000) (Real.log (57749 / 50000)) := by
  have h := reflection_log_9837_neg
  have he : Real.log (57749 / 50000) = -Real.log (50000 / 57749) := by
    rw [show ((57749 / 50000) : ℝ) = ((50000 / 57749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9838_neg : (168394983 / 1000000000) ≤ -Real.log (42251 / 50000) ∧
    -Real.log (42251 / 50000) ≤ (21049373 / 125000000) := by
  have h := checkLog_sound (w := (7749 / 92251)) (n := 12)
    (lo := (168394983 / 1000000000)) (hi := (21049373 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 42251) = 1/(42251 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9838 : Bounds (-21049373 / 125000000) (-168394983 / 1000000000) (Real.log (42251 / 50000)) := by
  have h := reflection_log_9838_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9839_neg : (72399833 / 500000000) ≤ -Real.log (31250 / 36119) ∧
    -Real.log (31250 / 36119) ≤ (144799667 / 1000000000) := by
  have h := checkLog_sound (w := (4869 / 67369)) (n := 12)
    (lo := (72399833 / 500000000)) (hi := (144799667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36119 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36119 / 31250) = 1/(31250 / 36119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9839 : Bounds (72399833 / 500000000) (144799667 / 1000000000) (Real.log (36119 / 31250)) := by
  have h := reflection_log_9839_neg
  have he : Real.log (36119 / 31250) = -Real.log (31250 / 36119) := by
    rw [show ((36119 / 31250) : ℝ) = ((31250 / 36119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9840_neg : (84687661 / 500000000) ≤ -Real.log (26381 / 31250) ∧
    -Real.log (26381 / 31250) ≤ (169375323 / 1000000000) := by
  have h := checkLog_sound (w := (4869 / 57631)) (n := 12)
    (lo := (84687661 / 500000000)) (hi := (169375323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 26381) = 1/(26381 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9840 : Bounds (-169375323 / 1000000000) (-84687661 / 500000000) (Real.log (26381 / 31250)) := by
  have h := reflection_log_9840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9841_neg : (4915131 / 200000000) ≤ -Real.log (952855339 / 976562500) ∧
    -Real.log (952855339 / 976562500) ≤ (3071957 / 125000000) := by
  have h := checkLog_sound (w := (23707161 / 1929417839)) (n := 12)
    (lo := (4915131 / 200000000)) (hi := (3071957 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 952855339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 952855339) = 1/(952855339 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9841 : Bounds (-3071957 / 125000000) (-4915131 / 200000000) (Real.log (952855339 / 976562500)) := by
  have h := reflection_log_9841_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9842_neg : (4862391 / 200000000) ≤ -Real.log (2439952999 / 2500000000) ∧
    -Real.log (2439952999 / 2500000000) ≤ (6077989 / 250000000) := by
  have h := checkLog_sound (w := (60047001 / 4939952999)) (n := 12)
    (lo := (4862391 / 200000000)) (hi := (6077989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2439952999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2439952999) = 1/(2439952999 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9842 : Bounds (-6077989 / 250000000) (-4862391 / 200000000) (Real.log (2439952999 / 2500000000)) := by
  have h := reflection_log_9842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9843_neg : (312478011 / 1000000000) ≤ -Real.log (500000000000 / 683403943101) ∧
    -Real.log (500000000000 / 683403943101) ≤ (78119503 / 250000000) := by
  have h := checkLog_sound (w := (183403943101 / 1183403943101)) (n := 12)
    (lo := (312478011 / 1000000000)) (hi := (78119503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683403943101 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683403943101 / 500000000000) = 1/(500000000000 / 683403943101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9843 : Bounds (312478011 / 1000000000) (78119503 / 250000000) (Real.log (683403943101 / 500000000000)) := by
  have h := reflection_log_9843_neg
  have he : Real.log (683403943101 / 500000000000) = -Real.log (500000000000 / 683403943101) := by
    rw [show ((683403943101 / 500000000000) : ℝ) = ((500000000000 / 683403943101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9844_neg : (78543747 / 250000000) ≤ -Real.log (500000000000 / 684564648801) ∧
    -Real.log (500000000000 / 684564648801) ≤ (314174989 / 1000000000) := by
  have h := checkLog_sound (w := (184564648801 / 1184564648801)) (n := 12)
    (lo := (78543747 / 250000000)) (hi := (314174989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684564648801 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684564648801 / 500000000000) = 1/(500000000000 / 684564648801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9844 : Bounds (78543747 / 250000000) (314174989 / 1000000000) (Real.log (684564648801 / 500000000000)) := by
  have h := reflection_log_9844_neg
  have he : Real.log (684564648801 / 500000000000) = -Real.log (500000000000 / 684564648801) := by
    rw [show ((684564648801 / 500000000000) : ℝ) = ((500000000000 / 684564648801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9845_neg : (315023237 / 500000000) ≤ -Real.log (500000000000 / 938848920863) ∧
    -Real.log (500000000000 / 938848920863) ≤ (25201859 / 40000000) := by
  have h := checkLog_sound (w := (438848920863 / 1438848920863)) (n := 12)
    (lo := (315023237 / 500000000)) (hi := (25201859 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((938848920863 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(938848920863 / 500000000000) = 1/(500000000000 / 938848920863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9845 : Bounds (315023237 / 500000000) (25201859 / 40000000) (Real.log (938848920863 / 500000000000)) := by
  have h := reflection_log_9845_neg
  have he : Real.log (938848920863 / 500000000000) = -Real.log (500000000000 / 938848920863) := by
    rw [show ((938848920863 / 500000000000) : ℝ) = ((500000000000 / 938848920863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9846_neg : (632252349 / 1000000000) ≤ -Real.log (250000000000 / 470461095101) ∧
    -Real.log (250000000000 / 470461095101) ≤ (12645047 / 20000000) := by
  have h := checkLog_sound (w := (220461095101 / 720461095101)) (n := 12)
    (lo := (632252349 / 1000000000)) (hi := (12645047 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((470461095101 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(470461095101 / 250000000000) = 1/(250000000000 / 470461095101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9846 : Bounds (632252349 / 1000000000) (12645047 / 20000000) (Real.log (470461095101 / 250000000000)) := by
  have h := reflection_log_9846_neg
  have he : Real.log (470461095101 / 250000000000) = -Real.log (250000000000 / 470461095101) := by
    rw [show ((470461095101 / 250000000000) : ℝ) = ((250000000000 / 470461095101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9847_neg : (133867217 / 500000000) ≤ -Real.log (1000 / 1307) ∧
    -Real.log (1000 / 1307) ≤ (53546887 / 200000000) := by
  have h := checkLog_sound (w := (307 / 2307)) (n := 12)
    (lo := (133867217 / 500000000)) (hi := (53546887 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1307 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1307 / 1000) = 1/(1000 / 1307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9847 : Bounds (133867217 / 500000000) (53546887 / 200000000) (Real.log (1307 / 1000)) := by
  have h := reflection_log_9847_neg
  have he : Real.log (1307 / 1000) = -Real.log (1000 / 1307) := by
    rw [show ((1307 / 1000) : ℝ) = ((1000 / 1307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9848_neg : (366725279 / 1000000000) ≤ -Real.log (693 / 1000) ∧
    -Real.log (693 / 1000) ≤ (2292033 / 6250000) := by
  have h := checkLog_sound (w := (307 / 1693)) (n := 12)
    (lo := (366725279 / 1000000000)) (hi := (2292033 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 693) = 1/(693 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9848 : Bounds (-2292033 / 6250000) (-366725279 / 1000000000) (Real.log (693 / 1000)) := by
  have h := reflection_log_9848_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9849_neg : (38369 / 125000000) ≤ -Real.log (1000000 / 1000307) ∧
    -Real.log (1000000 / 1000307) ≤ (306953 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 2000307)) (n := 12)
    (lo := (38369 / 125000000)) (hi := (306953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000307 / 1000000) = 1/(1000000 / 1000307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9849 : Bounds (38369 / 125000000) (306953 / 1000000000) (Real.log (1000307 / 1000000)) := by
  have h := reflection_log_9849_neg
  have he : Real.log (1000307 / 1000000) = -Real.log (1000000 / 1000307) := by
    rw [show ((1000307 / 1000000) : ℝ) = ((1000000 / 1000307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9850_neg : (307047 / 1000000000) ≤ -Real.log (999693 / 1000000) ∧
    -Real.log (999693 / 1000000) ≤ (38381 / 125000000) := by
  have h := checkLog_sound (w := (307 / 1999693)) (n := 12)
    (lo := (307047 / 1000000000)) (hi := (38381 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999693) = 1/(999693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9850 : Bounds (-38381 / 125000000) (-307047 / 1000000000) (Real.log (999693 / 1000000)) := by
  have h := reflection_log_9850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9851_neg : (144538343 / 1000000000) ≤ -Real.log (500000 / 577753) ∧
    -Real.log (500000 / 577753) ≤ (18067293 / 125000000) := by
  have h := checkLog_sound (w := (77753 / 1077753)) (n := 12)
    (lo := (144538343 / 1000000000)) (hi := (18067293 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577753 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(577753 / 500000) = 1/(500000 / 577753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9851 : Bounds (144538343 / 1000000000) (18067293 / 125000000) (Real.log (577753 / 500000)) := by
  have h := reflection_log_9851_neg
  have he : Real.log (577753 / 500000) = -Real.log (500000 / 577753) := by
    rw [show ((577753 / 500000) : ℝ) = ((500000 / 577753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9852_neg : (169017647 / 1000000000) ≤ -Real.log (422247 / 500000) ∧
    -Real.log (422247 / 500000) ≤ (10563603 / 62500000) := by
  have h := checkLog_sound (w := (77753 / 922247)) (n := 12)
    (lo := (169017647 / 1000000000)) (hi := (10563603 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 422247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 422247) = 1/(422247 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9852 : Bounds (-10563603 / 62500000) (-169017647 / 1000000000) (Real.log (422247 / 500000)) := by
  have h := reflection_log_9852_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9853_neg : (907847 / 6250000) ≤ -Real.log (200000 / 231267) ∧
    -Real.log (200000 / 231267) ≤ (145255521 / 1000000000) := by
  have h := checkLog_sound (w := (31267 / 431267)) (n := 12)
    (lo := (907847 / 6250000)) (hi := (145255521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231267 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231267 / 200000) = 1/(200000 / 231267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9853 : Bounds (907847 / 6250000) (145255521 / 1000000000) (Real.log (231267 / 200000)) := by
  have h := reflection_log_9853_neg
  have he : Real.log (231267 / 200000) = -Real.log (200000 / 231267) := by
    rw [show ((231267 / 200000) : ℝ) = ((200000 / 231267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9854_neg : (84999891 / 500000000) ≤ -Real.log (168733 / 200000) ∧
    -Real.log (168733 / 200000) ≤ (169999783 / 1000000000) := by
  have h := checkLog_sound (w := (31267 / 368733)) (n := 12)
    (lo := (84999891 / 500000000)) (hi := (169999783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 168733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 168733) = 1/(168733 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9854 : Bounds (-169999783 / 1000000000) (-84999891 / 500000000) (Real.log (168733 / 200000)) := by
  have h := reflection_log_9854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9855_neg : (24744261 / 1000000000) ≤ -Real.log (39022374711 / 40000000000) ∧
    -Real.log (39022374711 / 40000000000) ≤ (12372131 / 500000000) := by
  have h := checkLog_sound (w := (977625289 / 79022374711)) (n := 12)
    (lo := (24744261 / 1000000000)) (hi := (12372131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39022374711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39022374711) = 1/(39022374711 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9855 : Bounds (-12372131 / 500000000) (-24744261 / 1000000000) (Real.log (39022374711 / 40000000000)) := by
  have h := reflection_log_9855_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
