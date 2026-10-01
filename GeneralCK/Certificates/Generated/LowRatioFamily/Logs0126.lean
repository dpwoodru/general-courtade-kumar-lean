import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8064_neg : (29941 / 125000000) ≤ -Real.log (1999521 / 2000000) ∧
    -Real.log (1999521 / 2000000) ≤ (239529 / 1000000000) := by
  have h := checkLog_sound (w := (479 / 3999521)) (n := 12)
    (lo := (29941 / 125000000)) (hi := (239529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999521) = 1/(1999521 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8064 : Bounds (-239529 / 1000000000) (-29941 / 125000000) (Real.log (1999521 / 2000000)) := by
  have h := reflection_log_8064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8065_neg : (14236713 / 125000000) ≤ -Real.log (1000000 / 1120633) ∧
    -Real.log (1000000 / 1120633) ≤ (22778741 / 200000000) := by
  have h := checkLog_sound (w := (120633 / 2120633)) (n := 12)
    (lo := (14236713 / 125000000)) (hi := (22778741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1120633 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1120633 / 1000000) = 1/(1000000 / 1120633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8065 : Bounds (14236713 / 125000000) (22778741 / 200000000) (Real.log (1120633 / 1000000)) := by
  have h := reflection_log_8065_neg
  have he : Real.log (1120633 / 1000000) = -Real.log (1000000 / 1120633) := by
    rw [show ((1120633 / 1000000) : ℝ) = ((1000000 / 1120633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8066_neg : (32138237 / 250000000) ≤ -Real.log (879367 / 1000000) ∧
    -Real.log (879367 / 1000000) ≤ (128552949 / 1000000000) := by
  have h := checkLog_sound (w := (120633 / 1879367)) (n := 12)
    (lo := (32138237 / 250000000)) (hi := (128552949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 879367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 879367) = 1/(879367 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8066 : Bounds (-128552949 / 1000000000) (-32138237 / 250000000) (Real.log (879367 / 1000000)) := by
  have h := reflection_log_8066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8067_neg : (114336213 / 1000000000) ≤ -Real.log (1000000 / 1121129) ∧
    -Real.log (1000000 / 1121129) ≤ (57168107 / 500000000) := by
  have h := checkLog_sound (w := (121129 / 2121129)) (n := 12)
    (lo := (114336213 / 1000000000)) (hi := (57168107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1121129 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1121129 / 1000000) = 1/(1000000 / 1121129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8067 : Bounds (114336213 / 1000000000) (57168107 / 500000000) (Real.log (1121129 / 1000000)) := by
  have h := reflection_log_8067_neg
  have he : Real.log (1121129 / 1000000) = -Real.log (1000000 / 1121129) := by
    rw [show ((1121129 / 1000000) : ℝ) = ((1000000 / 1121129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8068_neg : (129117149 / 1000000000) ≤ -Real.log (878871 / 1000000) ∧
    -Real.log (878871 / 1000000) ≤ (2582343 / 20000000) := by
  have h := checkLog_sound (w := (121129 / 1878871)) (n := 12)
    (lo := (129117149 / 1000000000)) (hi := (2582343 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 878871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 878871) = 1/(878871 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8068 : Bounds (-2582343 / 20000000) (-129117149 / 1000000000) (Real.log (878871 / 1000000)) := by
  have h := reflection_log_8068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8069_neg : (1847617 / 125000000) ≤ -Real.log (985327765359 / 1000000000000) ∧
    -Real.log (985327765359 / 1000000000000) ≤ (14780937 / 1000000000) := by
  have h := checkLog_sound (w := (14672234641 / 1985327765359)) (n := 12)
    (lo := (1847617 / 125000000)) (hi := (14780937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985327765359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985327765359) = 1/(985327765359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8069 : Bounds (-14780937 / 1000000000) (-1847617 / 125000000) (Real.log (985327765359 / 1000000000000)) := by
  have h := reflection_log_8069_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8070_neg : (3664811 / 250000000) ≤ -Real.log (985447679311 / 1000000000000) ∧
    -Real.log (985447679311 / 1000000000000) ≤ (2931849 / 200000000) := by
  have h := checkLog_sound (w := (14552320689 / 1985447679311)) (n := 12)
    (lo := (3664811 / 250000000)) (hi := (2931849 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985447679311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985447679311) = 1/(985447679311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8070 : Bounds (-2931849 / 200000000) (-3664811 / 250000000) (Real.log (985447679311 / 1000000000000)) := by
  have h := reflection_log_8070_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8071_neg : (60611663 / 250000000) ≤ -Real.log (500000000000 / 637181631787) ∧
    -Real.log (500000000000 / 637181631787) ≤ (242446653 / 1000000000) := by
  have h := checkLog_sound (w := (137181631787 / 1137181631787)) (n := 12)
    (lo := (60611663 / 250000000)) (hi := (242446653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637181631787 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637181631787 / 500000000000) = 1/(500000000000 / 637181631787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8071 : Bounds (60611663 / 250000000) (242446653 / 1000000000) (Real.log (637181631787 / 500000000000)) := by
  have h := reflection_log_8071_neg
  have he : Real.log (637181631787 / 500000000000) = -Real.log (500000000000 / 637181631787) := by
    rw [show ((637181631787 / 500000000000) : ℝ) = ((500000000000 / 637181631787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8072_neg : (243453363 / 1000000000) ≤ -Real.log (500000000000 / 637823412083) ∧
    -Real.log (500000000000 / 637823412083) ≤ (60863341 / 250000000) := by
  have h := checkLog_sound (w := (137823412083 / 1137823412083)) (n := 12)
    (lo := (243453363 / 1000000000)) (hi := (60863341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637823412083 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637823412083 / 500000000000) = 1/(500000000000 / 637823412083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8072 : Bounds (243453363 / 1000000000) (60863341 / 250000000) (Real.log (637823412083 / 500000000000)) := by
  have h := reflection_log_8072_neg
  have he : Real.log (637823412083 / 500000000000) = -Real.log (500000000000 / 637823412083) := by
    rw [show ((637823412083 / 500000000000) : ℝ) = ((500000000000 / 637823412083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8073_neg : (487426523 / 1000000000) ≤ -Real.log (25000000000 / 40703022339) ∧
    -Real.log (25000000000 / 40703022339) ≤ (121856631 / 250000000) := by
  have h := checkLog_sound (w := (15703022339 / 65703022339)) (n := 12)
    (lo := (487426523 / 1000000000)) (hi := (121856631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40703022339 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40703022339 / 25000000000) = 1/(25000000000 / 40703022339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8073 : Bounds (487426523 / 1000000000) (121856631 / 250000000) (Real.log (40703022339 / 25000000000)) := by
  have h := reflection_log_8073_neg
  have he : Real.log (40703022339 / 25000000000) = -Real.log (25000000000 / 40703022339) := by
    rw [show ((40703022339 / 25000000000) : ℝ) = ((25000000000 / 40703022339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8074_neg : (488487239 / 1000000000) ≤ -Real.log (62500000000 / 101865548981) ∧
    -Real.log (62500000000 / 101865548981) ≤ (12212181 / 25000000) := by
  have h := checkLog_sound (w := (39365548981 / 164365548981)) (n := 12)
    (lo := (488487239 / 1000000000)) (hi := (12212181 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101865548981 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101865548981 / 62500000000) = 1/(62500000000 / 101865548981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8074 : Bounds (488487239 / 1000000000) (12212181 / 25000000) (Real.log (101865548981 / 62500000000)) := by
  have h := reflection_log_8074_neg
  have he : Real.log (101865548981 / 62500000000) = -Real.log (62500000000 / 101865548981) := by
    rw [show ((101865548981 / 62500000000) : ℝ) = ((62500000000 / 101865548981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8075_neg : (215111379 / 1000000000) ≤ -Real.log (25 / 31) ∧
    -Real.log (25 / 31) ≤ (10755569 / 50000000) := by
  have h := checkLog_sound (w := (3 / 28)) (n := 12)
    (lo := (215111379 / 1000000000)) (hi := (10755569 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31 / 25) = 1/(25 / 31) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8075 : Bounds (215111379 / 1000000000) (10755569 / 50000000) (Real.log (31 / 25)) := by
  have h := reflection_log_8075_neg
  have he : Real.log (31 / 25) = -Real.log (25 / 31) := by
    rw [show ((31 / 25) : ℝ) = ((25 / 31) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8076_neg : (54887369 / 200000000) ≤ -Real.log (19 / 25) ∧
    -Real.log (19 / 25) ≤ (137218423 / 500000000) := by
  have h := checkLog_sound (w := (3 / 22)) (n := 12)
    (lo := (54887369 / 200000000)) (hi := (137218423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 19) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 19) = 1/(19 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8076 : Bounds (-137218423 / 500000000) (-54887369 / 200000000) (Real.log (19 / 25)) := by
  have h := reflection_log_8076_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8077_neg : (239971 / 1000000000) ≤ -Real.log (12500 / 12503) ∧
    -Real.log (12500 / 12503) ≤ (59993 / 250000000) := by
  have h := checkLog_sound (w := (3 / 25003)) (n := 12)
    (lo := (239971 / 1000000000)) (hi := (59993 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12503 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12503 / 12500) = 1/(12500 / 12503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8077 : Bounds (239971 / 1000000000) (59993 / 250000000) (Real.log (12503 / 12500)) := by
  have h := reflection_log_8077_neg
  have he : Real.log (12503 / 12500) = -Real.log (12500 / 12503) := by
    rw [show ((12503 / 12500) : ℝ) = ((12500 / 12503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8078_neg : (60007 / 250000000) ≤ -Real.log (12497 / 12500) ∧
    -Real.log (12497 / 12500) ≤ (240029 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 24997)) (n := 12)
    (lo := (60007 / 250000000)) (hi := (240029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 12497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 12497) = 1/(12497 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8078 : Bounds (-240029 / 1000000000) (-60007 / 250000000) (Real.log (12497 / 12500)) := by
  have h := reflection_log_8078_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8079_neg : (891593 / 7812500) ≤ -Real.log (1000000 / 1120891) ∧
    -Real.log (1000000 / 1120891) ≤ (22824781 / 200000000) := by
  have h := checkLog_sound (w := (120891 / 2120891)) (n := 12)
    (lo := (891593 / 7812500)) (hi := (22824781 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1120891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1120891 / 1000000) = 1/(1000000 / 1120891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8079 : Bounds (891593 / 7812500) (22824781 / 200000000) (Real.log (1120891 / 1000000)) := by
  have h := reflection_log_8079_neg
  have he : Real.log (1120891 / 1000000) = -Real.log (1000000 / 1120891) := by
    rw [show ((1120891 / 1000000) : ℝ) = ((1000000 / 1120891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8080_neg : (8052899 / 62500000) ≤ -Real.log (879109 / 1000000) ∧
    -Real.log (879109 / 1000000) ≤ (25769277 / 200000000) := by
  have h := checkLog_sound (w := (120891 / 1879109)) (n := 12)
    (lo := (8052899 / 62500000)) (hi := (25769277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 879109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 879109) = 1/(879109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8080 : Bounds (-25769277 / 200000000) (-8052899 / 62500000) (Real.log (879109 / 1000000)) := by
  have h := reflection_log_8080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8081_neg : (114566311 / 1000000000) ≤ -Real.log (1000000 / 1121387) ∧
    -Real.log (1000000 / 1121387) ≤ (14320789 / 125000000) := by
  have h := checkLog_sound (w := (121387 / 2121387)) (n := 12)
    (lo := (114566311 / 1000000000)) (hi := (14320789 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1121387 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1121387 / 1000000) = 1/(1000000 / 1121387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8081 : Bounds (114566311 / 1000000000) (14320789 / 125000000) (Real.log (1121387 / 1000000)) := by
  have h := reflection_log_8081_neg
  have he : Real.log (1121387 / 1000000) = -Real.log (1000000 / 1121387) := by
    rw [show ((1121387 / 1000000) : ℝ) = ((1000000 / 1121387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8082_neg : (129410751 / 1000000000) ≤ -Real.log (878613 / 1000000) ∧
    -Real.log (878613 / 1000000) ≤ (2022043 / 15625000) := by
  have h := checkLog_sound (w := (121387 / 1878613)) (n := 12)
    (lo := (129410751 / 1000000000)) (hi := (2022043 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 878613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 878613) = 1/(878613 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8082 : Bounds (-2022043 / 15625000) (-129410751 / 1000000000) (Real.log (878613 / 1000000)) := by
  have h := reflection_log_8082_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8083_neg : (14844439 / 1000000000) ≤ -Real.log (985265196231 / 1000000000000) ∧
    -Real.log (985265196231 / 1000000000000) ≤ (371111 / 25000000) := by
  have h := checkLog_sound (w := (14734803769 / 1985265196231)) (n := 12)
    (lo := (14844439 / 1000000000)) (hi := (371111 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985265196231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985265196231) = 1/(985265196231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8083 : Bounds (-371111 / 25000000) (-14844439 / 1000000000) (Real.log (985265196231 / 1000000000000)) := by
  have h := reflection_log_8083_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8084_neg : (14722479 / 1000000000) ≤ -Real.log (985385366119 / 1000000000000) ∧
    -Real.log (985385366119 / 1000000000000) ≤ (184031 / 12500000) := by
  have h := checkLog_sound (w := (14614633881 / 1985385366119)) (n := 12)
    (lo := (14722479 / 1000000000)) (hi := (184031 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985385366119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985385366119) = 1/(985385366119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8084 : Bounds (-184031 / 12500000) (-14722479 / 1000000000) (Real.log (985385366119 / 1000000000000)) := by
  have h := reflection_log_8084_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8085_neg : (242970289 / 1000000000) ≤ -Real.log (125000000000 / 159378842669) ∧
    -Real.log (125000000000 / 159378842669) ≤ (24297029 / 100000000) := by
  have h := checkLog_sound (w := (34378842669 / 284378842669)) (n := 12)
    (lo := (242970289 / 1000000000)) (hi := (24297029 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159378842669 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159378842669 / 125000000000) = 1/(125000000000 / 159378842669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8085 : Bounds (242970289 / 1000000000) (24297029 / 100000000) (Real.log (159378842669 / 125000000000)) := by
  have h := reflection_log_8085_neg
  have he : Real.log (159378842669 / 125000000000) = -Real.log (125000000000 / 159378842669) := by
    rw [show ((159378842669 / 125000000000) : ℝ) = ((125000000000 / 159378842669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8086_neg : (243977063 / 1000000000) ≤ -Real.log (500000000000 / 638157527831) ∧
    -Real.log (500000000000 / 638157527831) ≤ (30497133 / 125000000) := by
  have h := checkLog_sound (w := (138157527831 / 1138157527831)) (n := 12)
    (lo := (243977063 / 1000000000)) (hi := (30497133 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((638157527831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(638157527831 / 500000000000) = 1/(500000000000 / 638157527831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8086 : Bounds (243977063 / 1000000000) (30497133 / 125000000) (Real.log (638157527831 / 500000000000)) := by
  have h := reflection_log_8086_neg
  have he : Real.log (638157527831 / 500000000000) = -Real.log (500000000000 / 638157527831) := by
    rw [show ((638157527831 / 500000000000) : ℝ) = ((500000000000 / 638157527831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8087_neg : (488487239 / 1000000000) ≤ -Real.log (500000000000 / 814924391847) ∧
    -Real.log (500000000000 / 814924391847) ≤ (12212181 / 25000000) := by
  have h := checkLog_sound (w := (314924391847 / 1314924391847)) (n := 12)
    (lo := (488487239 / 1000000000)) (hi := (12212181 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((814924391847 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(814924391847 / 500000000000) = 1/(500000000000 / 814924391847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8087 : Bounds (488487239 / 1000000000) (12212181 / 25000000) (Real.log (814924391847 / 500000000000)) := by
  have h := reflection_log_8087_neg
  have he : Real.log (814924391847 / 500000000000) = -Real.log (500000000000 / 814924391847) := by
    rw [show ((814924391847 / 500000000000) : ℝ) = ((500000000000 / 814924391847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8088_neg : (19581929 / 40000000) ≤ -Real.log (100000000000 / 163157894737) ∧
    -Real.log (100000000000 / 163157894737) ≤ (244774113 / 500000000) := by
  have h := checkLog_sound (w := (63157894737 / 263157894737)) (n := 12)
    (lo := (19581929 / 40000000)) (hi := (244774113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163157894737 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163157894737 / 100000000000) = 1/(100000000000 / 163157894737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8088 : Bounds (19581929 / 40000000) (244774113 / 500000000) (Real.log (163157894737 / 100000000000)) := by
  have h := reflection_log_8088_neg
  have he : Real.log (163157894737 / 100000000000) = -Real.log (100000000000 / 163157894737) := by
    rw [show ((163157894737 / 100000000000) : ℝ) = ((100000000000 / 163157894737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8089_neg : (53878631 / 250000000) ≤ -Real.log (2000 / 2481) ∧
    -Real.log (2000 / 2481) ≤ (8620581 / 40000000) := by
  have h := checkLog_sound (w := (481 / 4481)) (n := 12)
    (lo := (53878631 / 250000000)) (hi := (8620581 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2481 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2481 / 2000) = 1/(2000 / 2481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8089 : Bounds (53878631 / 250000000) (8620581 / 40000000) (Real.log (2481 / 2000)) := by
  have h := reflection_log_8089_neg
  have he : Real.log (2481 / 2000) = -Real.log (2000 / 2481) := by
    rw [show ((2481 / 2000) : ℝ) = ((2000 / 2481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8090_neg : (68773739 / 250000000) ≤ -Real.log (1519 / 2000) ∧
    -Real.log (1519 / 2000) ≤ (275094957 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 3519)) (n := 12)
    (lo := (68773739 / 250000000)) (hi := (275094957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1519) = 1/(1519 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8090 : Bounds (-275094957 / 1000000000) (-68773739 / 250000000) (Real.log (1519 / 2000)) := by
  have h := reflection_log_8090_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8091_neg : (240471 / 1000000000) ≤ -Real.log (2000000 / 2000481) ∧
    -Real.log (2000000 / 2000481) ≤ (30059 / 125000000) := by
  have h := checkLog_sound (w := (481 / 4000481)) (n := 12)
    (lo := (240471 / 1000000000)) (hi := (30059 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000481 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000481 / 2000000) = 1/(2000000 / 2000481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8091 : Bounds (240471 / 1000000000) (30059 / 125000000) (Real.log (2000481 / 2000000)) := by
  have h := reflection_log_8091_neg
  have he : Real.log (2000481 / 2000000) = -Real.log (2000000 / 2000481) := by
    rw [show ((2000481 / 2000000) : ℝ) = ((2000000 / 2000481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8092_neg : (15033 / 62500000) ≤ -Real.log (1999519 / 2000000) ∧
    -Real.log (1999519 / 2000000) ≤ (240529 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 3999519)) (n := 12)
    (lo := (15033 / 62500000)) (hi := (240529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999519) = 1/(1999519 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8092 : Bounds (-240529 / 1000000000) (-15033 / 62500000) (Real.log (1999519 / 2000000)) := by
  have h := reflection_log_8092_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8093_neg : (28588513 / 250000000) ≤ -Real.log (1000000 / 1121149) ∧
    -Real.log (1000000 / 1121149) ≤ (114354053 / 1000000000) := by
  have h := checkLog_sound (w := (121149 / 2121149)) (n := 12)
    (lo := (28588513 / 250000000)) (hi := (114354053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1121149 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1121149 / 1000000) = 1/(1000000 / 1121149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8093 : Bounds (28588513 / 250000000) (114354053 / 1000000000) (Real.log (1121149 / 1000000)) := by
  have h := reflection_log_8093_neg
  have he : Real.log (1121149 / 1000000) = -Real.log (1000000 / 1121149) := by
    rw [show ((1121149 / 1000000) : ℝ) = ((1000000 / 1121149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8094_neg : (64569953 / 500000000) ≤ -Real.log (878851 / 1000000) ∧
    -Real.log (878851 / 1000000) ≤ (129139907 / 1000000000) := by
  have h := checkLog_sound (w := (121149 / 1878851)) (n := 12)
    (lo := (64569953 / 500000000)) (hi := (129139907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 878851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 878851) = 1/(878851 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8094 : Bounds (-129139907 / 1000000000) (-64569953 / 500000000) (Real.log (878851 / 1000000)) := by
  have h := reflection_log_8094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8095_neg : (114796357 / 1000000000) ≤ -Real.log (200000 / 224329) ∧
    -Real.log (200000 / 224329) ≤ (57398179 / 500000000) := by
  have h := checkLog_sound (w := (24329 / 424329)) (n := 12)
    (lo := (114796357 / 1000000000)) (hi := (57398179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((224329 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(224329 / 200000) = 1/(200000 / 224329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8095 : Bounds (114796357 / 1000000000) (57398179 / 500000000) (Real.log (224329 / 200000)) := by
  have h := reflection_log_8095_neg
  have he : Real.log (224329 / 200000) = -Real.log (200000 / 224329) := by
    rw [show ((224329 / 200000) : ℝ) = ((200000 / 224329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8096_neg : (129704439 / 1000000000) ≤ -Real.log (175671 / 200000) ∧
    -Real.log (175671 / 200000) ≤ (3242611 / 25000000) := by
  have h := checkLog_sound (w := (24329 / 375671)) (n := 12)
    (lo := (129704439 / 1000000000)) (hi := (3242611 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 175671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 175671) = 1/(175671 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8096 : Bounds (-3242611 / 25000000) (-129704439 / 1000000000) (Real.log (175671 / 200000)) := by
  have h := reflection_log_8096_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8097_neg : (14908081 / 1000000000) ≤ -Real.log (39408099759 / 40000000000) ∧
    -Real.log (39408099759 / 40000000000) ≤ (7454041 / 500000000) := by
  have h := checkLog_sound (w := (591900241 / 79408099759)) (n := 12)
    (lo := (14908081 / 1000000000)) (hi := (7454041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39408099759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39408099759) = 1/(39408099759 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8097 : Bounds (-7454041 / 500000000) (-14908081 / 1000000000) (Real.log (39408099759 / 40000000000)) := by
  have h := reflection_log_8097_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8098_neg : (7392927 / 500000000) ≤ -Real.log (985322919799 / 1000000000000) ∧
    -Real.log (985322919799 / 1000000000000) ≤ (2957171 / 200000000) := by
  have h := checkLog_sound (w := (14677080201 / 1985322919799)) (n := 12)
    (lo := (7392927 / 500000000)) (hi := (2957171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985322919799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985322919799) = 1/(985322919799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8098 : Bounds (-2957171 / 200000000) (-7392927 / 500000000) (Real.log (985322919799 / 1000000000000)) := by
  have h := reflection_log_8098_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8099_neg : (121746979 / 500000000) ≤ -Real.log (500000000000 / 637849305513) ∧
    -Real.log (500000000000 / 637849305513) ≤ (243493959 / 1000000000) := by
  have h := checkLog_sound (w := (137849305513 / 1137849305513)) (n := 12)
    (lo := (121746979 / 500000000)) (hi := (243493959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637849305513 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637849305513 / 500000000000) = 1/(500000000000 / 637849305513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8099 : Bounds (121746979 / 500000000) (243493959 / 1000000000) (Real.log (637849305513 / 500000000000)) := by
  have h := reflection_log_8099_neg
  have he : Real.log (637849305513 / 500000000000) = -Real.log (500000000000 / 637849305513) := by
    rw [show ((637849305513 / 500000000000) : ℝ) = ((500000000000 / 637849305513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8100_neg : (61125199 / 250000000) ≤ -Real.log (25000000000 / 31924591993) ∧
    -Real.log (25000000000 / 31924591993) ≤ (244500797 / 1000000000) := by
  have h := checkLog_sound (w := (6924591993 / 56924591993)) (n := 12)
    (lo := (61125199 / 250000000)) (hi := (244500797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31924591993 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31924591993 / 25000000000) = 1/(25000000000 / 31924591993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8100 : Bounds (61125199 / 250000000) (244500797 / 1000000000) (Real.log (31924591993 / 25000000000)) := by
  have h := reflection_log_8100_neg
  have he : Real.log (31924591993 / 25000000000) = -Real.log (25000000000 / 31924591993) := by
    rw [show ((31924591993 / 25000000000) : ℝ) = ((25000000000 / 31924591993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8101_neg : (19581929 / 40000000) ≤ -Real.log (125000000000 / 203947368421) ∧
    -Real.log (125000000000 / 203947368421) ≤ (244774113 / 500000000) := by
  have h := checkLog_sound (w := (78947368421 / 328947368421)) (n := 12)
    (lo := (19581929 / 40000000)) (hi := (244774113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203947368421 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(203947368421 / 125000000000) = 1/(125000000000 / 203947368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8101 : Bounds (19581929 / 40000000) (244774113 / 500000000) (Real.log (203947368421 / 125000000000)) := by
  have h := reflection_log_8101_neg
  have he : Real.log (203947368421 / 125000000000) = -Real.log (125000000000 / 203947368421) := by
    rw [show ((203947368421 / 125000000000) : ℝ) = ((125000000000 / 203947368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8102_neg : (490609481 / 1000000000) ≤ -Real.log (62500000000 / 102081961817) ∧
    -Real.log (62500000000 / 102081961817) ≤ (245304741 / 500000000) := by
  have h := checkLog_sound (w := (39581961817 / 164581961817)) (n := 12)
    (lo := (490609481 / 1000000000)) (hi := (245304741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102081961817 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102081961817 / 62500000000) = 1/(62500000000 / 102081961817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8102 : Bounds (490609481 / 1000000000) (245304741 / 500000000) (Real.log (102081961817 / 62500000000)) := by
  have h := reflection_log_8102_neg
  have he : Real.log (102081961817 / 62500000000) = -Real.log (62500000000 / 102081961817) := by
    rw [show ((102081961817 / 62500000000) : ℝ) = ((62500000000 / 102081961817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8103_neg : (107958753 / 500000000) ≤ -Real.log (1000 / 1241) ∧
    -Real.log (1000 / 1241) ≤ (215917507 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 2241)) (n := 12)
    (lo := (107958753 / 500000000)) (hi := (215917507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241 / 1000) = 1/(1000 / 1241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8103 : Bounds (107958753 / 500000000) (215917507 / 1000000000) (Real.log (1241 / 1000)) := by
  have h := reflection_log_8103_neg
  have he : Real.log (1241 / 1000) = -Real.log (1000 / 1241) := by
    rw [show ((1241 / 1000) : ℝ) = ((1000 / 1241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8104_neg : (275753501 / 1000000000) ≤ -Real.log (759 / 1000) ∧
    -Real.log (759 / 1000) ≤ (137876751 / 500000000) := by
  have h := checkLog_sound (w := (241 / 1759)) (n := 12)
    (lo := (275753501 / 1000000000)) (hi := (137876751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 759) = 1/(759 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8104 : Bounds (-137876751 / 500000000) (-275753501 / 1000000000) (Real.log (759 / 1000)) := by
  have h := reflection_log_8104_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8105_neg : (24097 / 100000000) ≤ -Real.log (1000000 / 1000241) ∧
    -Real.log (1000000 / 1000241) ≤ (240971 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 2000241)) (n := 12)
    (lo := (24097 / 100000000)) (hi := (240971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000241 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000241 / 1000000) = 1/(1000000 / 1000241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8105 : Bounds (24097 / 100000000) (240971 / 1000000000) (Real.log (1000241 / 1000000)) := by
  have h := reflection_log_8105_neg
  have he : Real.log (1000241 / 1000000) = -Real.log (1000000 / 1000241) := by
    rw [show ((1000241 / 1000000) : ℝ) = ((1000000 / 1000241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8106_neg : (241029 / 1000000000) ≤ -Real.log (999759 / 1000000) ∧
    -Real.log (999759 / 1000000) ≤ (24103 / 100000000) := by
  have h := checkLog_sound (w := (241 / 1999759)) (n := 12)
    (lo := (241029 / 1000000000)) (hi := (24103 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999759) = 1/(999759 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8106 : Bounds (-24103 / 100000000) (-241029 / 1000000000) (Real.log (999759 / 1000000)) := by
  have h := reflection_log_8106_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8107_neg : (57292073 / 500000000) ≤ -Real.log (1000000 / 1121407) ∧
    -Real.log (1000000 / 1121407) ≤ (114584147 / 1000000000) := by
  have h := checkLog_sound (w := (121407 / 2121407)) (n := 12)
    (lo := (57292073 / 500000000)) (hi := (114584147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1121407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1121407 / 1000000) = 1/(1000000 / 1121407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8107 : Bounds (57292073 / 500000000) (114584147 / 1000000000) (Real.log (1121407 / 1000000)) := by
  have h := reflection_log_8107_neg
  have he : Real.log (1121407 / 1000000) = -Real.log (1000000 / 1121407) := by
    rw [show ((1121407 / 1000000) : ℝ) = ((1000000 / 1121407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8108_neg : (64716757 / 500000000) ≤ -Real.log (878593 / 1000000) ∧
    -Real.log (878593 / 1000000) ≤ (25886703 / 200000000) := by
  have h := checkLog_sound (w := (121407 / 1878593)) (n := 12)
    (lo := (64716757 / 500000000)) (hi := (25886703 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 878593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 878593) = 1/(878593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8108 : Bounds (-25886703 / 200000000) (-64716757 / 500000000) (Real.log (878593 / 1000000)) := by
  have h := reflection_log_8108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8109_neg : (115027241 / 1000000000) ≤ -Real.log (62500 / 70119) ∧
    -Real.log (62500 / 70119) ≤ (57513621 / 500000000) := by
  have h := checkLog_sound (w := (7619 / 132619)) (n := 12)
    (lo := (115027241 / 1000000000)) (hi := (57513621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70119 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70119 / 62500) = 1/(62500 / 70119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8109 : Bounds (115027241 / 1000000000) (57513621 / 500000000) (Real.log (70119 / 62500)) := by
  have h := reflection_log_8109_neg
  have he : Real.log (70119 / 62500) = -Real.log (62500 / 70119) := by
    rw [show ((70119 / 62500) : ℝ) = ((62500 / 70119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8110_neg : (129999351 / 1000000000) ≤ -Real.log (54881 / 62500) ∧
    -Real.log (54881 / 62500) ≤ (16249919 / 125000000) := by
  have h := checkLog_sound (w := (7619 / 117381)) (n := 12)
    (lo := (129999351 / 1000000000)) (hi := (16249919 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 54881) = 1/(54881 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8110 : Bounds (-16249919 / 125000000) (-129999351 / 1000000000) (Real.log (54881 / 62500)) := by
  have h := reflection_log_8110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8111_neg : (14972109 / 1000000000) ≤ -Real.log (3848200839 / 3906250000) ∧
    -Real.log (3848200839 / 3906250000) ≤ (1497211 / 100000000) := by
  have h := checkLog_sound (w := (58049161 / 7754450839)) (n := 12)
    (lo := (14972109 / 1000000000)) (hi := (1497211 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3848200839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3848200839) = 1/(3848200839 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8111 : Bounds (-1497211 / 100000000) (-14972109 / 1000000000) (Real.log (3848200839 / 3906250000)) := by
  have h := reflection_log_8111_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8112_neg : (14849367 / 1000000000) ≤ -Real.log (985260340351 / 1000000000000) ∧
    -Real.log (985260340351 / 1000000000000) ≤ (1856171 / 125000000) := by
  have h := checkLog_sound (w := (14739659649 / 1985260340351)) (n := 12)
    (lo := (14849367 / 1000000000)) (hi := (1856171 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985260340351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985260340351) = 1/(985260340351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8112 : Bounds (-1856171 / 125000000) (-14849367 / 1000000000) (Real.log (985260340351 / 1000000000000)) := by
  have h := reflection_log_8112_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8113_neg : (244017661 / 1000000000) ≤ -Real.log (500000000000 / 638183436471) ∧
    -Real.log (500000000000 / 638183436471) ≤ (122008831 / 500000000) := by
  have h := checkLog_sound (w := (138183436471 / 1138183436471)) (n := 12)
    (lo := (244017661 / 1000000000)) (hi := (122008831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((638183436471 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(638183436471 / 500000000000) = 1/(500000000000 / 638183436471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8113 : Bounds (244017661 / 1000000000) (122008831 / 500000000) (Real.log (638183436471 / 500000000000)) := by
  have h := reflection_log_8113_neg
  have he : Real.log (638183436471 / 500000000000) = -Real.log (500000000000 / 638183436471) := by
    rw [show ((638183436471 / 500000000000) : ℝ) = ((500000000000 / 638183436471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8114_neg : (245026593 / 1000000000) ≤ -Real.log (500000000000 / 638827645269) ∧
    -Real.log (500000000000 / 638827645269) ≤ (122513297 / 500000000) := by
  have h := checkLog_sound (w := (138827645269 / 1138827645269)) (n := 12)
    (lo := (245026593 / 1000000000)) (hi := (122513297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((638827645269 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(638827645269 / 500000000000) = 1/(500000000000 / 638827645269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8114 : Bounds (245026593 / 1000000000) (122513297 / 500000000) (Real.log (638827645269 / 500000000000)) := by
  have h := reflection_log_8114_neg
  have he : Real.log (638827645269 / 500000000000) = -Real.log (500000000000 / 638827645269) := by
    rw [show ((638827645269 / 500000000000) : ℝ) = ((500000000000 / 638827645269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8115_neg : (490609481 / 1000000000) ≤ -Real.log (100000000000 / 163331138907) ∧
    -Real.log (100000000000 / 163331138907) ≤ (245304741 / 500000000) := by
  have h := checkLog_sound (w := (63331138907 / 263331138907)) (n := 12)
    (lo := (490609481 / 1000000000)) (hi := (245304741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163331138907 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163331138907 / 100000000000) = 1/(100000000000 / 163331138907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8115 : Bounds (490609481 / 1000000000) (245304741 / 500000000) (Real.log (163331138907 / 100000000000)) := by
  have h := reflection_log_8115_neg
  have he : Real.log (163331138907 / 100000000000) = -Real.log (100000000000 / 163331138907) := by
    rw [show ((163331138907 / 100000000000) : ℝ) = ((100000000000 / 163331138907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8116_neg : (491671007 / 1000000000) ≤ -Real.log (250000000000 / 408761528327) ∧
    -Real.log (250000000000 / 408761528327) ≤ (15364719 / 31250000) := by
  have h := checkLog_sound (w := (158761528327 / 658761528327)) (n := 12)
    (lo := (491671007 / 1000000000)) (hi := (15364719 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((408761528327 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(408761528327 / 250000000000) = 1/(250000000000 / 408761528327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8116 : Bounds (491671007 / 1000000000) (15364719 / 31250000) (Real.log (408761528327 / 250000000000)) := by
  have h := reflection_log_8116_neg
  have he : Real.log (408761528327 / 250000000000) = -Real.log (250000000000 / 408761528327) := by
    rw [show ((408761528327 / 250000000000) : ℝ) = ((250000000000 / 408761528327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8117_neg : (8652813 / 40000000) ≤ -Real.log (2000 / 2483) ∧
    -Real.log (2000 / 2483) ≤ (108160163 / 500000000) := by
  have h := checkLog_sound (w := (483 / 4483)) (n := 12)
    (lo := (8652813 / 40000000)) (hi := (108160163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2483 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2483 / 2000) = 1/(2000 / 2483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8117 : Bounds (8652813 / 40000000) (108160163 / 500000000) (Real.log (2483 / 2000)) := by
  have h := reflection_log_8117_neg
  have he : Real.log (2483 / 2000) = -Real.log (2000 / 2483) := by
    rw [show ((2483 / 2000) : ℝ) = ((2000 / 2483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8118_neg : (863789 / 3125000) ≤ -Real.log (1517 / 2000) ∧
    -Real.log (1517 / 2000) ≤ (276412481 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 3517)) (n := 12)
    (lo := (863789 / 3125000)) (hi := (276412481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1517) = 1/(1517 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8118 : Bounds (-276412481 / 1000000000) (-863789 / 3125000) (Real.log (1517 / 2000)) := by
  have h := reflection_log_8118_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8119_neg : (24147 / 100000000) ≤ -Real.log (2000000 / 2000483) ∧
    -Real.log (2000000 / 2000483) ≤ (241471 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 4000483)) (n := 12)
    (lo := (24147 / 100000000)) (hi := (241471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000483 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000483 / 2000000) = 1/(2000000 / 2000483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8119 : Bounds (24147 / 100000000) (241471 / 1000000000) (Real.log (2000483 / 2000000)) := by
  have h := reflection_log_8119_neg
  have he : Real.log (2000483 / 2000000) = -Real.log (2000000 / 2000483) := by
    rw [show ((2000483 / 2000000) : ℝ) = ((2000000 / 2000483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8120_neg : (241529 / 1000000000) ≤ -Real.log (1999517 / 2000000) ∧
    -Real.log (1999517 / 2000000) ≤ (24153 / 100000000) := by
  have h := checkLog_sound (w := (483 / 3999517)) (n := 12)
    (lo := (241529 / 1000000000)) (hi := (24153 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999517) = 1/(1999517 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8120 : Bounds (-24153 / 100000000) (-241529 / 1000000000) (Real.log (1999517 / 2000000)) := by
  have h := reflection_log_8120_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8121_neg : (114813297 / 1000000000) ≤ -Real.log (15625 / 17526) ∧
    -Real.log (15625 / 17526) ≤ (57406649 / 500000000) := by
  have h := checkLog_sound (w := (1901 / 33151)) (n := 12)
    (lo := (114813297 / 1000000000)) (hi := (57406649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17526 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17526 / 15625) = 1/(15625 / 17526) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8121 : Bounds (114813297 / 1000000000) (57406649 / 500000000) (Real.log (17526 / 15625)) := by
  have h := reflection_log_8121_neg
  have he : Real.log (17526 / 15625) = -Real.log (15625 / 17526) := by
    rw [show ((17526 / 15625) : ℝ) = ((15625 / 17526) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8122_neg : (12972607 / 100000000) ≤ -Real.log (13724 / 15625) ∧
    -Real.log (13724 / 15625) ≤ (129726071 / 1000000000) := by
  have h := checkLog_sound (w := (1901 / 29349)) (n := 12)
    (lo := (12972607 / 100000000)) (hi := (129726071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13724) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13724) = 1/(13724 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8122 : Bounds (-129726071 / 1000000000) (-12972607 / 100000000) (Real.log (13724 / 15625)) := by
  have h := reflection_log_8122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8123_neg : (115257181 / 1000000000) ≤ -Real.log (500000 / 561081) ∧
    -Real.log (500000 / 561081) ≤ (57628591 / 500000000) := by
  have h := checkLog_sound (w := (61081 / 1061081)) (n := 12)
    (lo := (115257181 / 1000000000)) (hi := (57628591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((561081 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(561081 / 500000) = 1/(500000 / 561081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8123 : Bounds (115257181 / 1000000000) (57628591 / 500000000) (Real.log (561081 / 500000)) := by
  have h := reflection_log_8123_neg
  have he : Real.log (561081 / 500000) = -Real.log (500000 / 561081) := by
    rw [show ((561081 / 500000) : ℝ) = ((500000 / 561081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8124_neg : (32573303 / 250000000) ≤ -Real.log (438919 / 500000) ∧
    -Real.log (438919 / 500000) ≤ (130293213 / 1000000000) := by
  have h := checkLog_sound (w := (61081 / 938919)) (n := 12)
    (lo := (32573303 / 250000000)) (hi := (130293213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 438919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 438919) = 1/(438919 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8124 : Bounds (-130293213 / 1000000000) (-32573303 / 250000000) (Real.log (438919 / 500000)) := by
  have h := reflection_log_8124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8125_neg : (1503603 / 100000000) ≤ -Real.log (246269111439 / 250000000000) ∧
    -Real.log (246269111439 / 250000000000) ≤ (15036031 / 1000000000) := by
  have h := checkLog_sound (w := (3730888561 / 496269111439)) (n := 12)
    (lo := (1503603 / 100000000)) (hi := (15036031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246269111439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246269111439) = 1/(246269111439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8125 : Bounds (-15036031 / 1000000000) (-1503603 / 100000000) (Real.log (246269111439 / 250000000000)) := by
  have h := reflection_log_8125_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8126_neg : (14912773 / 1000000000) ≤ -Real.log (240526824 / 244140625) ∧
    -Real.log (240526824 / 244140625) ≤ (7456387 / 500000000) := by
  have h := checkLog_sound (w := (3613801 / 484667449)) (n := 12)
    (lo := (14912773 / 1000000000)) (hi := (7456387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 240526824) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 240526824) = 1/(240526824 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8126 : Bounds (-7456387 / 500000000) (-14912773 / 1000000000) (Real.log (240526824 / 244140625)) := by
  have h := reflection_log_8126_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8127_neg : (244539367 / 1000000000) ≤ -Real.log (250000000000 / 319258233751) ∧
    -Real.log (250000000000 / 319258233751) ≤ (30567421 / 125000000) := by
  have h := checkLog_sound (w := (69258233751 / 569258233751)) (n := 12)
    (lo := (244539367 / 1000000000)) (hi := (30567421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319258233751 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319258233751 / 250000000000) = 1/(250000000000 / 319258233751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8127 : Bounds (244539367 / 1000000000) (30567421 / 125000000) (Real.log (319258233751 / 250000000000)) := by
  have h := reflection_log_8127_neg
  have he : Real.log (319258233751 / 250000000000) = -Real.log (250000000000 / 319258233751) := by
    rw [show ((319258233751 / 250000000000) : ℝ) = ((250000000000 / 319258233751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
