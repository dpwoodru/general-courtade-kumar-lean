import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1088_neg : (19901181 / 125000000) ≤ -Real.log (250000000000 / 293145879207) ∧
    -Real.log (250000000000 / 293145879207) ≤ (159209449 / 1000000000) := by
  have h := checkLog_sound (w := (43145879207 / 543145879207)) (n := 12)
    (lo := (19901181 / 125000000)) (hi := (159209449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293145879207 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293145879207 / 250000000000) = 1/(250000000000 / 293145879207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1088 : Bounds (19901181 / 125000000) (159209449 / 1000000000) (Real.log (293145879207 / 250000000000)) := by
  have h := reflection_log_1088_neg
  have he : Real.log (293145879207 / 250000000000) = -Real.log (250000000000 / 293145879207) := by
    rw [show ((293145879207 / 250000000000) : ℝ) = ((250000000000 / 293145879207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1089_neg : (159232263 / 500000000) ≤ -Real.log (500000000000 / 687507421921) ∧
    -Real.log (500000000000 / 687507421921) ≤ (318464527 / 1000000000) := by
  have h := checkLog_sound (w := (187507421921 / 1187507421921)) (n := 12)
    (lo := (159232263 / 500000000)) (hi := (318464527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687507421921 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687507421921 / 500000000000) = 1/(500000000000 / 687507421921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1089 : Bounds (159232263 / 500000000) (318464527 / 1000000000) (Real.log (687507421921 / 500000000000)) := by
  have h := reflection_log_1089_neg
  have he : Real.log (687507421921 / 500000000000) = -Real.log (500000000000 / 687507421921) := by
    rw [show ((687507421921 / 500000000000) : ℝ) = ((500000000000 / 687507421921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1090_neg : (318669643 / 1000000000) ≤ -Real.log (250000000000 / 343824228029) ∧
    -Real.log (250000000000 / 343824228029) ≤ (79667411 / 250000000) := by
  have h := checkLog_sound (w := (93824228029 / 593824228029)) (n := 12)
    (lo := (318669643 / 1000000000)) (hi := (79667411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343824228029 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343824228029 / 250000000000) = 1/(250000000000 / 343824228029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1090 : Bounds (318669643 / 1000000000) (79667411 / 250000000) (Real.log (343824228029 / 250000000000)) := by
  have h := reflection_log_1090_neg
  have he : Real.log (343824228029 / 250000000000) = -Real.log (250000000000 / 343824228029) := by
    rw [show ((343824228029 / 250000000000) : ℝ) = ((250000000000 / 343824228029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1091_neg : (146780731 / 1000000000) ≤ -Real.log (10000 / 11581) ∧
    -Real.log (10000 / 11581) ≤ (36695183 / 250000000) := by
  have h := checkLog_sound (w := (1581 / 21581)) (n := 12)
    (lo := (146780731 / 1000000000)) (hi := (36695183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11581 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11581 / 10000) = 1/(10000 / 11581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1091 : Bounds (146780731 / 1000000000) (36695183 / 250000000) (Real.log (11581 / 10000)) := by
  have h := reflection_log_1091_neg
  have he : Real.log (11581 / 10000) = -Real.log (10000 / 11581) := by
    rw [show ((11581 / 10000) : ℝ) = ((10000 / 11581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1092_neg : (43023509 / 250000000) ≤ -Real.log (8419 / 10000) ∧
    -Real.log (8419 / 10000) ≤ (172094037 / 1000000000) := by
  have h := checkLog_sound (w := (1581 / 18419)) (n := 12)
    (lo := (43023509 / 250000000)) (hi := (172094037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8419) = 1/(8419 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1092 : Bounds (-172094037 / 1000000000) (-43023509 / 250000000) (Real.log (8419 / 10000)) := by
  have h := reflection_log_1092_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1093_neg : (158087 / 1000000000) ≤ -Real.log (10000000 / 10001581) ∧
    -Real.log (10000000 / 10001581) ≤ (19761 / 125000000) := by
  have h := checkLog_sound (w := (1581 / 20001581)) (n := 12)
    (lo := (158087 / 1000000000)) (hi := (19761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001581 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001581 / 10000000) = 1/(10000000 / 10001581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1093 : Bounds (158087 / 1000000000) (19761 / 125000000) (Real.log (10001581 / 10000000)) := by
  have h := reflection_log_1093_neg
  have he : Real.log (10001581 / 10000000) = -Real.log (10000000 / 10001581) := by
    rw [show ((10001581 / 10000000) : ℝ) = ((10000000 / 10001581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1094_neg : (4941 / 31250000) ≤ -Real.log (9998419 / 10000000) ∧
    -Real.log (9998419 / 10000000) ≤ (158113 / 1000000000) := by
  have h := checkLog_sound (w := (1581 / 19998419)) (n := 12)
    (lo := (4941 / 31250000)) (hi := (158113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998419) = 1/(9998419 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1094 : Bounds (-158113 / 1000000000) (-4941 / 31250000) (Real.log (9998419 / 10000000)) := by
  have h := reflection_log_1094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1095_neg : (3051729 / 40000000) ≤ -Real.log (1000000 / 1079279) ∧
    -Real.log (1000000 / 1079279) ≤ (38146613 / 500000000) := by
  have h := checkLog_sound (w := (79279 / 2079279)) (n := 12)
    (lo := (3051729 / 40000000)) (hi := (38146613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079279 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079279 / 1000000) = 1/(1000000 / 1079279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1095 : Bounds (3051729 / 40000000) (38146613 / 500000000) (Real.log (1079279 / 1000000)) := by
  have h := reflection_log_1095_neg
  have he : Real.log (1079279 / 1000000) = -Real.log (1000000 / 1079279) := by
    rw [show ((1079279 / 1000000) : ℝ) = ((1000000 / 1079279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1096_neg : (4129911 / 50000000) ≤ -Real.log (920721 / 1000000) ∧
    -Real.log (920721 / 1000000) ≤ (82598221 / 1000000000) := by
  have h := checkLog_sound (w := (79279 / 1920721)) (n := 12)
    (lo := (4129911 / 50000000)) (hi := (82598221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920721) = 1/(920721 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1096 : Bounds (-82598221 / 1000000000) (-4129911 / 50000000) (Real.log (920721 / 1000000)) := by
  have h := reflection_log_1096_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1097_neg : (38243427 / 500000000) ≤ -Real.log (15625 / 16867) ∧
    -Real.log (15625 / 16867) ≤ (15297371 / 200000000) := by
  have h := checkLog_sound (w := (621 / 16246)) (n := 12)
    (lo := (38243427 / 500000000)) (hi := (15297371 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16867 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16867 / 15625) = 1/(15625 / 16867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1097 : Bounds (38243427 / 500000000) (15297371 / 200000000) (Real.log (16867 / 15625)) := by
  have h := reflection_log_1097_neg
  have he : Real.log (16867 / 15625) = -Real.log (15625 / 16867) := by
    rw [show ((16867 / 15625) : ℝ) = ((15625 / 16867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1098_neg : (41412621 / 500000000) ≤ -Real.log (14383 / 15625) ∧
    -Real.log (14383 / 15625) ≤ (82825243 / 1000000000) := by
  have h := checkLog_sound (w := (621 / 15004)) (n := 12)
    (lo := (41412621 / 500000000)) (hi := (82825243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 14383) = 1/(14383 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1098 : Bounds (-82825243 / 1000000000) (-41412621 / 500000000) (Real.log (14383 / 15625)) := by
  have h := reflection_log_1098_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1099_neg : (6338387 / 1000000000) ≤ -Real.log (242598061 / 244140625) ∧
    -Real.log (242598061 / 244140625) ≤ (1584597 / 250000000) := by
  have h := checkLog_sound (w := (771282 / 243369343)) (n := 12)
    (lo := (6338387 / 1000000000)) (hi := (1584597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 242598061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 242598061) = 1/(242598061 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1099 : Bounds (-1584597 / 250000000) (-6338387 / 1000000000) (Real.log (242598061 / 244140625)) := by
  have h := reflection_log_1099_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1100_neg : (3152497 / 500000000) ≤ -Real.log (993714840159 / 1000000000000) ∧
    -Real.log (993714840159 / 1000000000000) ≤ (1260999 / 200000000) := by
  have h := checkLog_sound (w := (6285159841 / 1993714840159)) (n := 12)
    (lo := (3152497 / 500000000)) (hi := (1260999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993714840159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993714840159) = 1/(993714840159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1100 : Bounds (-1260999 / 200000000) (-3152497 / 500000000) (Real.log (993714840159 / 1000000000000)) := by
  have h := reflection_log_1100_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1101_neg : (31778289 / 200000000) ≤ -Real.log (500000000000 / 586105345701) ∧
    -Real.log (500000000000 / 586105345701) ≤ (79445723 / 500000000) := by
  have h := checkLog_sound (w := (86105345701 / 1086105345701)) (n := 12)
    (lo := (31778289 / 200000000)) (hi := (79445723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586105345701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586105345701 / 500000000000) = 1/(500000000000 / 586105345701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1101 : Bounds (31778289 / 200000000) (79445723 / 500000000) (Real.log (586105345701 / 500000000000)) := by
  have h := reflection_log_1101_neg
  have he : Real.log (586105345701 / 500000000000) = -Real.log (500000000000 / 586105345701) := by
    rw [show ((586105345701 / 500000000000) : ℝ) = ((500000000000 / 586105345701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1102_neg : (4978503 / 31250000) ≤ -Real.log (500000000000 / 586351943267) ∧
    -Real.log (500000000000 / 586351943267) ≤ (159312097 / 1000000000) := by
  have h := checkLog_sound (w := (86351943267 / 1086351943267)) (n := 12)
    (lo := (4978503 / 31250000)) (hi := (159312097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586351943267 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586351943267 / 500000000000) = 1/(500000000000 / 586351943267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1102 : Bounds (4978503 / 31250000) (159312097 / 1000000000) (Real.log (586351943267 / 500000000000)) := by
  have h := reflection_log_1102_neg
  have he : Real.log (586351943267 / 500000000000) = -Real.log (500000000000 / 586351943267) := by
    rw [show ((586351943267 / 500000000000) : ℝ) = ((500000000000 / 586351943267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1103_neg : (318669643 / 1000000000) ≤ -Real.log (500000000000 / 687648456057) ∧
    -Real.log (500000000000 / 687648456057) ≤ (79667411 / 250000000) := by
  have h := checkLog_sound (w := (187648456057 / 1187648456057)) (n := 12)
    (lo := (318669643 / 1000000000)) (hi := (79667411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687648456057 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687648456057 / 500000000000) = 1/(500000000000 / 687648456057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1103 : Bounds (318669643 / 1000000000) (79667411 / 250000000) (Real.log (687648456057 / 500000000000)) := by
  have h := reflection_log_1103_neg
  have he : Real.log (687648456057 / 500000000000) = -Real.log (500000000000 / 687648456057) := by
    rw [show ((687648456057 / 500000000000) : ℝ) = ((500000000000 / 687648456057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1104_neg : (318874767 / 1000000000) ≤ -Real.log (500000000000 / 687789523697) ∧
    -Real.log (500000000000 / 687789523697) ≤ (19929673 / 62500000) := by
  have h := checkLog_sound (w := (187789523697 / 1187789523697)) (n := 12)
    (lo := (318874767 / 1000000000)) (hi := (19929673 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687789523697 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687789523697 / 500000000000) = 1/(500000000000 / 687789523697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1104 : Bounds (318874767 / 1000000000) (19929673 / 62500000) (Real.log (687789523697 / 500000000000)) := by
  have h := reflection_log_1104_neg
  have he : Real.log (687789523697 / 500000000000) = -Real.log (500000000000 / 687789523697) := by
    rw [show ((687789523697 / 500000000000) : ℝ) = ((500000000000 / 687789523697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1105_neg : (5874683 / 40000000) ≤ -Real.log (5000 / 5791) ∧
    -Real.log (5000 / 5791) ≤ (36716769 / 250000000) := by
  have h := checkLog_sound (w := (791 / 10791)) (n := 12)
    (lo := (5874683 / 40000000)) (hi := (36716769 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5791 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5791 / 5000) = 1/(5000 / 5791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1105 : Bounds (5874683 / 40000000) (36716769 / 250000000) (Real.log (5791 / 5000)) := by
  have h := reflection_log_1105_neg
  have he : Real.log (5791 / 5000) = -Real.log (5000 / 5791) := by
    rw [show ((5791 / 5000) : ℝ) = ((5000 / 5791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1106_neg : (86106411 / 500000000) ≤ -Real.log (4209 / 5000) ∧
    -Real.log (4209 / 5000) ≤ (172212823 / 1000000000) := by
  have h := checkLog_sound (w := (791 / 9209)) (n := 12)
    (lo := (86106411 / 500000000)) (hi := (172212823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4209) = 1/(4209 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1106 : Bounds (-172212823 / 1000000000) (-86106411 / 500000000) (Real.log (4209 / 5000)) := by
  have h := reflection_log_1106_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1107_neg : (158187 / 1000000000) ≤ -Real.log (5000000 / 5000791) ∧
    -Real.log (5000000 / 5000791) ≤ (39547 / 250000000) := by
  have h := checkLog_sound (w := (791 / 10000791)) (n := 12)
    (lo := (158187 / 1000000000)) (hi := (39547 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000791 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000791 / 5000000) = 1/(5000000 / 5000791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1107 : Bounds (158187 / 1000000000) (39547 / 250000000) (Real.log (5000791 / 5000000)) := by
  have h := reflection_log_1107_neg
  have he : Real.log (5000791 / 5000000) = -Real.log (5000000 / 5000791) := by
    rw [show ((5000791 / 5000000) : ℝ) = ((5000000 / 5000791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1108_neg : (39553 / 250000000) ≤ -Real.log (4999209 / 5000000) ∧
    -Real.log (4999209 / 5000000) ≤ (158213 / 1000000000) := by
  have h := checkLog_sound (w := (791 / 9999209)) (n := 12)
    (lo := (39553 / 250000000)) (hi := (158213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999209) = 1/(4999209 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1108 : Bounds (-158213 / 1000000000) (-39553 / 250000000) (Real.log (4999209 / 5000000)) := by
  have h := reflection_log_1108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1109_neg : (38170239 / 500000000) ≤ -Real.log (100000 / 107933) ∧
    -Real.log (100000 / 107933) ≤ (76340479 / 1000000000) := by
  have h := checkLog_sound (w := (7933 / 207933)) (n := 12)
    (lo := (38170239 / 500000000)) (hi := (76340479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107933 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107933 / 100000) = 1/(100000 / 107933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1109 : Bounds (38170239 / 500000000) (76340479 / 1000000000) (Real.log (107933 / 100000)) := by
  have h := reflection_log_1109_neg
  have he : Real.log (107933 / 100000) = -Real.log (100000 / 107933) := by
    rw [show ((107933 / 100000) : ℝ) = ((100000 / 107933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1110_neg : (82653613 / 1000000000) ≤ -Real.log (92067 / 100000) ∧
    -Real.log (92067 / 100000) ≤ (41326807 / 500000000) := by
  have h := checkLog_sound (w := (7933 / 192067)) (n := 12)
    (lo := (82653613 / 1000000000)) (hi := (41326807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 92067) = 1/(92067 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1110 : Bounds (-41326807 / 500000000) (-82653613 / 1000000000) (Real.log (92067 / 100000)) := by
  have h := reflection_log_1110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1111_neg : (38267049 / 500000000) ≤ -Real.log (1000000 / 1079539) ∧
    -Real.log (1000000 / 1079539) ≤ (76534099 / 1000000000) := by
  have h := checkLog_sound (w := (79539 / 2079539)) (n := 12)
    (lo := (38267049 / 500000000)) (hi := (76534099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079539 / 1000000) = 1/(1000000 / 1079539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1111 : Bounds (38267049 / 500000000) (76534099 / 1000000000) (Real.log (1079539 / 1000000)) := by
  have h := reflection_log_1111_neg
  have he : Real.log (1079539 / 1000000) = -Real.log (1000000 / 1079539) := by
    rw [show ((1079539 / 1000000) : ℝ) = ((1000000 / 1079539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1112_neg : (82880647 / 1000000000) ≤ -Real.log (920461 / 1000000) ∧
    -Real.log (920461 / 1000000) ≤ (10360081 / 125000000) := by
  have h := checkLog_sound (w := (79539 / 1920461)) (n := 12)
    (lo := (82880647 / 1000000000)) (hi := (10360081 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920461) = 1/(920461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1112 : Bounds (-10360081 / 125000000) (-82880647 / 1000000000) (Real.log (920461 / 1000000)) := by
  have h := reflection_log_1112_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1113_neg : (6346549 / 1000000000) ≤ -Real.log (993673547479 / 1000000000000) ∧
    -Real.log (993673547479 / 1000000000000) ≤ (126931 / 20000000) := by
  have h := checkLog_sound (w := (6326452521 / 1993673547479)) (n := 12)
    (lo := (6346549 / 1000000000)) (hi := (126931 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993673547479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993673547479) = 1/(993673547479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1113 : Bounds (-126931 / 20000000) (-6346549 / 1000000000) (Real.log (993673547479 / 1000000000000)) := by
  have h := reflection_log_1113_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1114_neg : (3156567 / 500000000) ≤ -Real.log (9937067511 / 10000000000) ∧
    -Real.log (9937067511 / 10000000000) ≤ (1262627 / 200000000) := by
  have h := checkLog_sound (w := (62932489 / 19937067511)) (n := 12)
    (lo := (3156567 / 500000000)) (hi := (1262627 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9937067511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9937067511) = 1/(9937067511 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1114 : Bounds (-1262627 / 200000000) (-3156567 / 500000000) (Real.log (9937067511 / 10000000000)) := by
  have h := reflection_log_1114_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1115_neg : (158994091 / 1000000000) ≤ -Real.log (5000000000 / 5861655099) ∧
    -Real.log (5000000000 / 5861655099) ≤ (39748523 / 250000000) := by
  have h := checkLog_sound (w := (861655099 / 10861655099)) (n := 12)
    (lo := (158994091 / 1000000000)) (hi := (39748523 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5861655099 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5861655099 / 5000000000) = 1/(5000000000 / 5861655099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1115 : Bounds (158994091 / 1000000000) (39748523 / 250000000) (Real.log (5861655099 / 5000000000)) := by
  have h := reflection_log_1115_neg
  have he : Real.log (5861655099 / 5000000000) = -Real.log (5000000000 / 5861655099) := by
    rw [show ((5861655099 / 5000000000) : ℝ) = ((5000000000 / 5861655099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1116_neg : (31882949 / 200000000) ≤ -Real.log (500000000000 / 586412134789) ∧
    -Real.log (500000000000 / 586412134789) ≤ (79707373 / 500000000) := by
  have h := checkLog_sound (w := (86412134789 / 1086412134789)) (n := 12)
    (lo := (31882949 / 200000000)) (hi := (79707373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586412134789 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586412134789 / 500000000000) = 1/(500000000000 / 586412134789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1116 : Bounds (31882949 / 200000000) (79707373 / 500000000) (Real.log (586412134789 / 500000000000)) := by
  have h := reflection_log_1116_neg
  have he : Real.log (586412134789 / 500000000000) = -Real.log (500000000000 / 586412134789) := by
    rw [show ((586412134789 / 500000000000) : ℝ) = ((500000000000 / 586412134789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1117_neg : (318874767 / 1000000000) ≤ -Real.log (31250000000 / 42986845231) ∧
    -Real.log (31250000000 / 42986845231) ≤ (19929673 / 62500000) := by
  have h := checkLog_sound (w := (11736845231 / 74236845231)) (n := 12)
    (lo := (318874767 / 1000000000)) (hi := (19929673 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42986845231 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42986845231 / 31250000000) = 1/(31250000000 / 42986845231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1117 : Bounds (318874767 / 1000000000) (19929673 / 62500000) (Real.log (42986845231 / 31250000000)) := by
  have h := reflection_log_1117_neg
  have he : Real.log (42986845231 / 31250000000) = -Real.log (31250000000 / 42986845231) := by
    rw [show ((42986845231 / 31250000000) : ℝ) = ((31250000000 / 42986845231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1118_neg : (159539949 / 500000000) ≤ -Real.log (125000000000 / 171982656213) ∧
    -Real.log (125000000000 / 171982656213) ≤ (319079899 / 1000000000) := by
  have h := checkLog_sound (w := (46982656213 / 296982656213)) (n := 12)
    (lo := (159539949 / 500000000)) (hi := (319079899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171982656213 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171982656213 / 125000000000) = 1/(125000000000 / 171982656213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1118 : Bounds (159539949 / 500000000) (319079899 / 1000000000) (Real.log (171982656213 / 125000000000)) := by
  have h := reflection_log_1118_neg
  have he : Real.log (171982656213 / 125000000000) = -Real.log (125000000000 / 171982656213) := by
    rw [show ((171982656213 / 125000000000) : ℝ) = ((125000000000 / 171982656213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1119_neg : (36738353 / 250000000) ≤ -Real.log (10000 / 11583) ∧
    -Real.log (10000 / 11583) ≤ (146953413 / 1000000000) := by
  have h := checkLog_sound (w := (1583 / 21583)) (n := 12)
    (lo := (36738353 / 250000000)) (hi := (146953413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11583 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11583 / 10000) = 1/(10000 / 11583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1119 : Bounds (36738353 / 250000000) (146953413 / 1000000000) (Real.log (11583 / 10000)) := by
  have h := reflection_log_1119_neg
  have he : Real.log (11583 / 10000) = -Real.log (10000 / 11583) := by
    rw [show ((11583 / 10000) : ℝ) = ((10000 / 11583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1120_neg : (86165811 / 500000000) ≤ -Real.log (8417 / 10000) ∧
    -Real.log (8417 / 10000) ≤ (172331623 / 1000000000) := by
  have h := checkLog_sound (w := (1583 / 18417)) (n := 12)
    (lo := (86165811 / 500000000)) (hi := (172331623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8417) = 1/(8417 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1120 : Bounds (-172331623 / 1000000000) (-86165811 / 500000000) (Real.log (8417 / 10000)) := by
  have h := reflection_log_1120_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1121_neg : (158287 / 1000000000) ≤ -Real.log (10000000 / 10001583) ∧
    -Real.log (10000000 / 10001583) ≤ (9893 / 62500000) := by
  have h := checkLog_sound (w := (1583 / 20001583)) (n := 12)
    (lo := (158287 / 1000000000)) (hi := (9893 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001583 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001583 / 10000000) = 1/(10000000 / 10001583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1121 : Bounds (158287 / 1000000000) (9893 / 62500000) (Real.log (10001583 / 10000000)) := by
  have h := reflection_log_1121_neg
  have he : Real.log (10001583 / 10000000) = -Real.log (10000000 / 10001583) := by
    rw [show ((10001583 / 10000000) : ℝ) = ((10000000 / 10001583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1122_neg : (19789 / 125000000) ≤ -Real.log (9998417 / 10000000) ∧
    -Real.log (9998417 / 10000000) ≤ (158313 / 1000000000) := by
  have h := checkLog_sound (w := (1583 / 19998417)) (n := 12)
    (lo := (19789 / 125000000)) (hi := (158313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998417) = 1/(9998417 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1122 : Bounds (-158313 / 1000000000) (-19789 / 125000000) (Real.log (9998417 / 10000000)) := by
  have h := reflection_log_1122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1123_neg : (38193401 / 500000000) ≤ -Real.log (50000 / 53969) ∧
    -Real.log (50000 / 53969) ≤ (76386803 / 1000000000) := by
  have h := checkLog_sound (w := (3969 / 103969)) (n := 12)
    (lo := (38193401 / 500000000)) (hi := (76386803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53969 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53969 / 50000) = 1/(50000 / 53969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1123 : Bounds (38193401 / 500000000) (76386803 / 1000000000) (Real.log (53969 / 50000)) := by
  have h := reflection_log_1123_neg
  have he : Real.log (53969 / 50000) = -Real.log (50000 / 53969) := by
    rw [show ((53969 / 50000) : ℝ) = ((50000 / 53969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1124_neg : (41353961 / 500000000) ≤ -Real.log (46031 / 50000) ∧
    -Real.log (46031 / 50000) ≤ (82707923 / 1000000000) := by
  have h := checkLog_sound (w := (3969 / 96031)) (n := 12)
    (lo := (41353961 / 500000000)) (hi := (82707923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 46031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 46031) = 1/(46031 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1124 : Bounds (-82707923 / 1000000000) (-41353961 / 500000000) (Real.log (46031 / 50000)) := by
  have h := reflection_log_1124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1125_neg : (76581339 / 1000000000) ≤ -Real.log (100000 / 107959) ∧
    -Real.log (100000 / 107959) ≤ (3829067 / 50000000) := by
  have h := checkLog_sound (w := (7959 / 207959)) (n := 12)
    (lo := (76581339 / 1000000000)) (hi := (3829067 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107959 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107959 / 100000) = 1/(100000 / 107959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1125 : Bounds (76581339 / 1000000000) (3829067 / 50000000) (Real.log (107959 / 100000)) := by
  have h := reflection_log_1125_neg
  have he : Real.log (107959 / 100000) = -Real.log (100000 / 107959) := by
    rw [show ((107959 / 100000) : ℝ) = ((100000 / 107959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1126_neg : (10367007 / 125000000) ≤ -Real.log (92041 / 100000) ∧
    -Real.log (92041 / 100000) ≤ (82936057 / 1000000000) := by
  have h := checkLog_sound (w := (7959 / 192041)) (n := 12)
    (lo := (10367007 / 125000000)) (hi := (82936057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 92041) = 1/(92041 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1126 : Bounds (-82936057 / 1000000000) (-10367007 / 125000000) (Real.log (92041 / 100000)) := by
  have h := reflection_log_1126_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1127_neg : (1588679 / 250000000) ≤ -Real.log (9936654319 / 10000000000) ∧
    -Real.log (9936654319 / 10000000000) ≤ (6354717 / 1000000000) := by
  have h := checkLog_sound (w := (63345681 / 19936654319)) (n := 12)
    (lo := (1588679 / 250000000)) (hi := (6354717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9936654319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9936654319) = 1/(9936654319 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1127 : Bounds (-6354717 / 1000000000) (-1588679 / 250000000) (Real.log (9936654319 / 10000000000)) := by
  have h := reflection_log_1127_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1128_neg : (39507 / 6250000) ≤ -Real.log (2484247039 / 2500000000) ∧
    -Real.log (2484247039 / 2500000000) ≤ (6321121 / 1000000000) := by
  have h := checkLog_sound (w := (15752961 / 4984247039)) (n := 12)
    (lo := (39507 / 6250000)) (hi := (6321121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2484247039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2484247039) = 1/(2484247039 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1128 : Bounds (-6321121 / 1000000000) (-39507 / 6250000) (Real.log (2484247039 / 2500000000)) := by
  have h := reflection_log_1128_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1129_neg : (6363789 / 40000000) ≤ -Real.log (500000000000 / 586224500879) ∧
    -Real.log (500000000000 / 586224500879) ≤ (79547363 / 500000000) := by
  have h := checkLog_sound (w := (86224500879 / 1086224500879)) (n := 12)
    (lo := (6363789 / 40000000)) (hi := (79547363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586224500879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586224500879 / 500000000000) = 1/(500000000000 / 586224500879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1129 : Bounds (6363789 / 40000000) (79547363 / 500000000) (Real.log (586224500879 / 500000000000)) := by
  have h := reflection_log_1129_neg
  have he : Real.log (586224500879 / 500000000000) = -Real.log (500000000000 / 586224500879) := by
    rw [show ((586224500879 / 500000000000) : ℝ) = ((500000000000 / 586224500879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1130_neg : (31903479 / 200000000) ≤ -Real.log (500000000000 / 586472332983) ∧
    -Real.log (500000000000 / 586472332983) ≤ (39879349 / 250000000) := by
  have h := checkLog_sound (w := (86472332983 / 1086472332983)) (n := 12)
    (lo := (31903479 / 200000000)) (hi := (39879349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586472332983 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586472332983 / 500000000000) = 1/(500000000000 / 586472332983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1130 : Bounds (31903479 / 200000000) (39879349 / 250000000) (Real.log (586472332983 / 500000000000)) := by
  have h := reflection_log_1130_neg
  have he : Real.log (586472332983 / 500000000000) = -Real.log (500000000000 / 586472332983) := by
    rw [show ((586472332983 / 500000000000) : ℝ) = ((500000000000 / 586472332983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1131_neg : (159539949 / 500000000) ≤ -Real.log (500000000000 / 687930624851) ∧
    -Real.log (500000000000 / 687930624851) ≤ (319079899 / 1000000000) := by
  have h := checkLog_sound (w := (187930624851 / 1187930624851)) (n := 12)
    (lo := (159539949 / 500000000)) (hi := (319079899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687930624851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687930624851 / 500000000000) = 1/(500000000000 / 687930624851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1131 : Bounds (159539949 / 500000000) (319079899 / 1000000000) (Real.log (687930624851 / 500000000000)) := by
  have h := reflection_log_1131_neg
  have he : Real.log (687930624851 / 500000000000) = -Real.log (500000000000 / 687930624851) := by
    rw [show ((687930624851 / 500000000000) : ℝ) = ((500000000000 / 687930624851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1132_neg : (63857007 / 200000000) ≤ -Real.log (100000000000 / 137614351907) ∧
    -Real.log (100000000000 / 137614351907) ≤ (79821259 / 250000000) := by
  have h := checkLog_sound (w := (37614351907 / 237614351907)) (n := 12)
    (lo := (63857007 / 200000000)) (hi := (79821259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137614351907 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137614351907 / 100000000000) = 1/(100000000000 / 137614351907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1132 : Bounds (63857007 / 200000000) (79821259 / 250000000) (Real.log (137614351907 / 100000000000)) := by
  have h := reflection_log_1132_neg
  have he : Real.log (137614351907 / 100000000000) = -Real.log (100000000000 / 137614351907) := by
    rw [show ((137614351907 / 100000000000) : ℝ) = ((100000000000 / 137614351907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1133_neg : (73519871 / 500000000) ≤ -Real.log (625 / 724) ∧
    -Real.log (625 / 724) ≤ (147039743 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 1349)) (n := 12)
    (lo := (73519871 / 500000000)) (hi := (147039743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724 / 625) = 1/(625 / 724) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1133 : Bounds (73519871 / 500000000) (147039743 / 1000000000) (Real.log (724 / 625)) := by
  have h := reflection_log_1133_neg
  have he : Real.log (724 / 625) = -Real.log (625 / 724) := by
    rw [show ((724 / 625) : ℝ) = ((625 / 724) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1134_neg : (43112609 / 250000000) ≤ -Real.log (526 / 625) ∧
    -Real.log (526 / 625) ≤ (172450437 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 1151)) (n := 12)
    (lo := (43112609 / 250000000)) (hi := (172450437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 526) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 526) = 1/(526 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1134 : Bounds (-172450437 / 1000000000) (-43112609 / 250000000) (Real.log (526 / 625)) := by
  have h := reflection_log_1134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1135_neg : (158387 / 1000000000) ≤ -Real.log (625000 / 625099) ∧
    -Real.log (625000 / 625099) ≤ (39597 / 250000000) := by
  have h := checkLog_sound (w := (99 / 1250099)) (n := 12)
    (lo := (158387 / 1000000000)) (hi := (39597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625099 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625099 / 625000) = 1/(625000 / 625099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1135 : Bounds (158387 / 1000000000) (39597 / 250000000) (Real.log (625099 / 625000)) := by
  have h := reflection_log_1135_neg
  have he : Real.log (625099 / 625000) = -Real.log (625000 / 625099) := by
    rw [show ((625099 / 625000) : ℝ) = ((625000 / 625099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1136_neg : (39603 / 250000000) ≤ -Real.log (624901 / 625000) ∧
    -Real.log (624901 / 625000) ≤ (158413 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 1249901)) (n := 12)
    (lo := (39603 / 250000000)) (hi := (158413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624901) = 1/(624901 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1136 : Bounds (-158413 / 1000000000) (-39603 / 250000000) (Real.log (624901 / 625000)) := by
  have h := reflection_log_1136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1137_neg : (1528681 / 20000000) ≤ -Real.log (1000000 / 1079431) ∧
    -Real.log (1000000 / 1079431) ≤ (76434051 / 1000000000) := by
  have h := checkLog_sound (w := (79431 / 2079431)) (n := 12)
    (lo := (1528681 / 20000000)) (hi := (76434051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079431 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079431 / 1000000) = 1/(1000000 / 1079431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1137 : Bounds (1528681 / 20000000) (76434051 / 1000000000) (Real.log (1079431 / 1000000)) := by
  have h := reflection_log_1137_neg
  have he : Real.log (1079431 / 1000000) = -Real.log (1000000 / 1079431) := by
    rw [show ((1079431 / 1000000) : ℝ) = ((1000000 / 1079431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1138_neg : (82763321 / 1000000000) ≤ -Real.log (920569 / 1000000) ∧
    -Real.log (920569 / 1000000) ≤ (41381661 / 500000000) := by
  have h := checkLog_sound (w := (79431 / 1920569)) (n := 12)
    (lo := (82763321 / 1000000000)) (hi := (41381661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920569) = 1/(920569 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1138 : Bounds (-41381661 / 500000000) (-82763321 / 1000000000) (Real.log (920569 / 1000000)) := by
  have h := reflection_log_1138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1139_neg : (19156913 / 250000000) ≤ -Real.log (25000 / 26991) ∧
    -Real.log (25000 / 26991) ≤ (76627653 / 1000000000) := by
  have h := checkLog_sound (w := (1991 / 51991)) (n := 12)
    (lo := (19156913 / 250000000)) (hi := (76627653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26991 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26991 / 25000) = 1/(25000 / 26991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1139 : Bounds (19156913 / 250000000) (76627653 / 1000000000) (Real.log (26991 / 25000)) := by
  have h := reflection_log_1139_neg
  have he : Real.log (26991 / 25000) = -Real.log (25000 / 26991) := by
    rw [show ((26991 / 25000) : ℝ) = ((25000 / 26991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1140_neg : (82990381 / 1000000000) ≤ -Real.log (23009 / 25000) ∧
    -Real.log (23009 / 25000) ≤ (41495191 / 500000000) := by
  have h := checkLog_sound (w := (1991 / 48009)) (n := 12)
    (lo := (82990381 / 1000000000)) (hi := (41495191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 23009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 23009) = 1/(23009 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1140 : Bounds (-41495191 / 500000000) (-82990381 / 1000000000) (Real.log (23009 / 25000)) := by
  have h := reflection_log_1140_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1141_neg : (795341 / 125000000) ≤ -Real.log (621035919 / 625000000) ∧
    -Real.log (621035919 / 625000000) ≤ (6362729 / 1000000000) := by
  have h := checkLog_sound (w := (3964081 / 1246035919)) (n := 12)
    (lo := (795341 / 125000000)) (hi := (6362729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 621035919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 621035919) = 1/(621035919 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1141 : Bounds (-6362729 / 1000000000) (-795341 / 125000000) (Real.log (621035919 / 625000000)) := by
  have h := reflection_log_1141_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1142_neg : (6329271 / 1000000000) ≤ -Real.log (993690716239 / 1000000000000) ∧
    -Real.log (993690716239 / 1000000000000) ≤ (791159 / 125000000) := by
  have h := checkLog_sound (w := (6309283761 / 1993690716239)) (n := 12)
    (lo := (6329271 / 1000000000)) (hi := (791159 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993690716239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993690716239) = 1/(993690716239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1142 : Bounds (-791159 / 125000000) (-6329271 / 1000000000) (Real.log (993690716239 / 1000000000000)) := by
  have h := reflection_log_1142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1143_neg : (39799343 / 250000000) ≤ -Real.log (12500000000 / 14657116957) ∧
    -Real.log (12500000000 / 14657116957) ≤ (159197373 / 1000000000) := by
  have h := checkLog_sound (w := (2157116957 / 27157116957)) (n := 12)
    (lo := (39799343 / 250000000)) (hi := (159197373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14657116957 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14657116957 / 12500000000) = 1/(12500000000 / 14657116957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1143 : Bounds (39799343 / 250000000) (159197373 / 1000000000) (Real.log (14657116957 / 12500000000)) := by
  have h := reflection_log_1143_neg
  have he : Real.log (14657116957 / 12500000000) = -Real.log (12500000000 / 14657116957) := by
    rw [show ((14657116957 / 12500000000) : ℝ) = ((12500000000 / 14657116957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1144_neg : (159618033 / 1000000000) ≤ -Real.log (100000000000 / 117306271459) ∧
    -Real.log (100000000000 / 117306271459) ≤ (79809017 / 500000000) := by
  have h := checkLog_sound (w := (17306271459 / 217306271459)) (n := 12)
    (lo := (159618033 / 1000000000)) (hi := (79809017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117306271459 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117306271459 / 100000000000) = 1/(100000000000 / 117306271459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1144 : Bounds (159618033 / 1000000000) (79809017 / 500000000) (Real.log (117306271459 / 100000000000)) := by
  have h := reflection_log_1144_neg
  have he : Real.log (117306271459 / 100000000000) = -Real.log (100000000000 / 117306271459) := by
    rw [show ((117306271459 / 100000000000) : ℝ) = ((100000000000 / 117306271459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1145_neg : (63857007 / 200000000) ≤ -Real.log (250000000000 / 344035879767) ∧
    -Real.log (250000000000 / 344035879767) ≤ (79821259 / 250000000) := by
  have h := checkLog_sound (w := (94035879767 / 594035879767)) (n := 12)
    (lo := (63857007 / 200000000)) (hi := (79821259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344035879767 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344035879767 / 250000000000) = 1/(250000000000 / 344035879767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1145 : Bounds (63857007 / 200000000) (79821259 / 250000000) (Real.log (344035879767 / 250000000000)) := by
  have h := reflection_log_1145_neg
  have he : Real.log (344035879767 / 250000000000) = -Real.log (250000000000 / 344035879767) := by
    rw [show ((344035879767 / 250000000000) : ℝ) = ((250000000000 / 344035879767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1146_neg : (319490179 / 1000000000) ≤ -Real.log (500000000000 / 688212927757) ∧
    -Real.log (500000000000 / 688212927757) ≤ (15974509 / 50000000) := by
  have h := checkLog_sound (w := (188212927757 / 1188212927757)) (n := 12)
    (lo := (319490179 / 1000000000)) (hi := (15974509 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688212927757 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688212927757 / 500000000000) = 1/(500000000000 / 688212927757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1146 : Bounds (319490179 / 1000000000) (15974509 / 50000000) (Real.log (688212927757 / 500000000000)) := by
  have h := reflection_log_1146_neg
  have he : Real.log (688212927757 / 500000000000) = -Real.log (500000000000 / 688212927757) := by
    rw [show ((688212927757 / 500000000000) : ℝ) = ((500000000000 / 688212927757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1147_neg : (9195379 / 62500000) ≤ -Real.log (2000 / 2317) ∧
    -Real.log (2000 / 2317) ≤ (29425213 / 200000000) := by
  have h := checkLog_sound (w := (317 / 4317)) (n := 12)
    (lo := (9195379 / 62500000)) (hi := (29425213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2317 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2317 / 2000) = 1/(2000 / 2317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1147 : Bounds (9195379 / 62500000) (29425213 / 200000000) (Real.log (2317 / 2000)) := by
  have h := reflection_log_1147_neg
  have he : Real.log (2317 / 2000) = -Real.log (2000 / 2317) := by
    rw [show ((2317 / 2000) : ℝ) = ((2000 / 2317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1148_neg : (34513853 / 200000000) ≤ -Real.log (1683 / 2000) ∧
    -Real.log (1683 / 2000) ≤ (86284633 / 500000000) := by
  have h := checkLog_sound (w := (317 / 3683)) (n := 12)
    (lo := (34513853 / 200000000)) (hi := (86284633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1683) = 1/(1683 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1148 : Bounds (-86284633 / 500000000) (-34513853 / 200000000) (Real.log (1683 / 2000)) := by
  have h := reflection_log_1148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1149_neg : (158487 / 1000000000) ≤ -Real.log (2000000 / 2000317) ∧
    -Real.log (2000000 / 2000317) ≤ (19811 / 125000000) := by
  have h := checkLog_sound (w := (317 / 4000317)) (n := 12)
    (lo := (158487 / 1000000000)) (hi := (19811 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000317 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000317 / 2000000) = 1/(2000000 / 2000317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1149 : Bounds (158487 / 1000000000) (19811 / 125000000) (Real.log (2000317 / 2000000)) := by
  have h := reflection_log_1149_neg
  have he : Real.log (2000317 / 2000000) = -Real.log (2000000 / 2000317) := by
    rw [show ((2000317 / 2000000) : ℝ) = ((2000000 / 2000317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1150_neg : (9907 / 62500000) ≤ -Real.log (1999683 / 2000000) ∧
    -Real.log (1999683 / 2000000) ≤ (158513 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 3999683)) (n := 12)
    (lo := (9907 / 62500000)) (hi := (158513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999683) = 1/(1999683 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1150 : Bounds (-158513 / 1000000000) (-9907 / 62500000) (Real.log (1999683 / 2000000)) := by
  have h := reflection_log_1150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1151_neg : (4780081 / 62500000) ≤ -Real.log (500000 / 539741) ∧
    -Real.log (500000 / 539741) ≤ (76481297 / 1000000000) := by
  have h := checkLog_sound (w := (39741 / 1039741)) (n := 12)
    (lo := (4780081 / 62500000)) (hi := (76481297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539741 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539741 / 500000) = 1/(500000 / 539741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1151 : Bounds (4780081 / 62500000) (76481297 / 1000000000) (Real.log (539741 / 500000)) := by
  have h := reflection_log_1151_neg
  have he : Real.log (539741 / 500000) = -Real.log (500000 / 539741) := by
    rw [show ((539741 / 500000) : ℝ) = ((500000 / 539741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
