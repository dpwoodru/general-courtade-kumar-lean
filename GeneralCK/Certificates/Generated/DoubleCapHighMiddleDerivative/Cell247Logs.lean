import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell247
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (83279601 / 250000000) ≤ -Real.log (640 / 893) ∧
    -Real.log (640 / 893) ≤ (66623681 / 200000000) := by
  have h := checkLog_sound (w := (253 / 1533)) (n := 12)
    (lo := (83279601 / 250000000)) (hi := (66623681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((893 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(893 / 640) = 1/(640 / 893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (83279601 / 250000000) (66623681 / 200000000) (Real.log (893 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (893 / 640) = -Real.log (640 / 893) := by
    rw [show ((893 / 640) : ℝ) = ((640 / 893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (503043483 / 1000000000) ≤ -Real.log (387 / 640) ∧
    -Real.log (387 / 640) ≤ (125760871 / 250000000) := by
  have h := checkLog_sound (w := (253 / 1027)) (n := 12)
    (lo := (503043483 / 1000000000)) (hi := (125760871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 387) = 1/(387 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-125760871 / 250000000) (-503043483 / 1000000000) (Real.log (387 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (332698383 / 1000000000) ≤ -Real.log (5120 / 7141) ∧
    -Real.log (5120 / 7141) ≤ (20793649 / 62500000) := by
  have h := checkLog_sound (w := (2021 / 12261)) (n := 12)
    (lo := (332698383 / 1000000000)) (hi := (20793649 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7141 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7141 / 5120) = 1/(5120 / 7141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (332698383 / 1000000000) (20793649 / 62500000) (Real.log (7141 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7141 / 5120) = -Real.log (5120 / 7141) := by
    rw [show ((7141 / 5120) : ℝ) = ((5120 / 7141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (6275937 / 12500000) ≤ -Real.log (3099 / 5120) ∧
    -Real.log (3099 / 5120) ≤ (502074961 / 1000000000) := by
  have h := checkLog_sound (w := (2021 / 8219)) (n := 12)
    (lo := (6275937 / 12500000)) (hi := (502074961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3099) = 1/(3099 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-502074961 / 1000000000) (-6275937 / 12500000) (Real.log (3099 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (49536479 / 200000000) ≤ -Real.log (1000000 / 1281053) ∧
    -Real.log (1000000 / 1281053) ≤ (61920599 / 250000000) := by
  have h := checkLog_sound (w := (281053 / 2281053)) (n := 12)
    (lo := (49536479 / 200000000)) (hi := (61920599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281053 / 1000000) = 1/(1000000 / 1281053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (49536479 / 200000000) (61920599 / 250000000) (Real.log (1281053 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1281053 / 1000000) = -Real.log (1000000 / 1281053) := by
    rw [show ((1281053 / 1000000) : ℝ) = ((1000000 / 1281053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (329967637 / 1000000000) ≤ -Real.log (718947 / 1000000) ∧
    -Real.log (718947 / 1000000) ≤ (164983819 / 500000000) := by
  have h := checkLog_sound (w := (281053 / 1718947)) (n := 12)
    (lo := (329967637 / 1000000000)) (hi := (164983819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 718947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 718947) = 1/(718947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-164983819 / 500000000) (-329967637 / 1000000000) (Real.log (718947 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (124006659 / 500000000) ≤ -Real.log (1000000 / 1281477) ∧
    -Real.log (1000000 / 1281477) ≤ (248013319 / 1000000000) := by
  have h := checkLog_sound (w := (281477 / 2281477)) (n := 12)
    (lo := (124006659 / 500000000)) (hi := (248013319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281477 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281477 / 1000000) = 1/(1000000 / 1281477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (124006659 / 500000000) (248013319 / 1000000000) (Real.log (1281477 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1281477 / 1000000) = -Real.log (1000000 / 1281477) := by
    rw [show ((1281477 / 1000000) : ℝ) = ((1000000 / 1281477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (165278781 / 500000000) ≤ -Real.log (718523 / 1000000) ∧
    -Real.log (718523 / 1000000) ≤ (330557563 / 1000000000) := by
  have h := checkLog_sound (w := (281477 / 1718523)) (n := 12)
    (lo := (165278781 / 500000000)) (hi := (330557563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 718523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 718523) = 1/(718523 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-330557563 / 1000000000) (-165278781 / 500000000) (Real.log (718523 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (9248361 / 50000000) ≤ -Real.log (1000000 / 1203179) ∧
    -Real.log (1000000 / 1203179) ≤ (184967221 / 1000000000) := by
  have h := checkLog_sound (w := (203179 / 2203179)) (n := 12)
    (lo := (9248361 / 50000000)) (hi := (184967221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203179 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203179 / 1000000) = 1/(1000000 / 1203179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (9248361 / 50000000) (184967221 / 1000000000) (Real.log (1203179 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1203179 / 1000000) = -Real.log (1000000 / 1203179) := by
    rw [show ((1203179 / 1000000) : ℝ) = ((1000000 / 1203179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (227125217 / 1000000000) ≤ -Real.log (796821 / 1000000) ∧
    -Real.log (796821 / 1000000) ≤ (113562609 / 500000000) := by
  have h := checkLog_sound (w := (203179 / 1796821)) (n := 12)
    (lo := (227125217 / 1000000000)) (hi := (113562609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 796821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 796821) = 1/(796821 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-113562609 / 500000000) (-227125217 / 1000000000) (Real.log (796821 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (92616989 / 500000000) ≤ -Real.log (2000 / 2407) ∧
    -Real.log (2000 / 2407) ≤ (185233979 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 4407)) (n := 12)
    (lo := (92616989 / 500000000)) (hi := (185233979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2407 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2407 / 2000) = 1/(2000 / 2407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (92616989 / 500000000) (185233979 / 1000000000) (Real.log (2407 / 2000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (2407 / 2000) = -Real.log (2000 / 2407) := by
    rw [show ((2407 / 2000) : ℝ) = ((2000 / 2407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (227528149 / 1000000000) ≤ -Real.log (1593 / 2000) ∧
    -Real.log (1593 / 2000) ≤ (4550563 / 20000000) := by
  have h := checkLog_sound (w := (407 / 3593)) (n := 12)
    (lo := (227528149 / 1000000000)) (hi := (4550563 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1593) = 1/(1593 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4550563 / 20000000) (-227528149 / 1000000000) (Real.log (1593 / 2000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (834773343 / 1000000000) ≤ -Real.log (500000000000 / 1152145853501) ∧
    -Real.log (500000000000 / 1152145853501) ≤ (166954669 / 200000000) := by
  have h := checkLog_sound (w := (152145853501 / 2152145853501)) (n := 12)
    (lo := (141626163 / 1000000000)) (hi := (35406541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152145853501 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1152145853501 / 1000000000000) = 1/(500000000000 / 1152145853501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (834773343 / 1000000000) (166954669 / 200000000) (Real.log (1152145853501 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1152145853501 / 500000000000) = -Real.log (500000000000 / 1152145853501) := by
    rw [show ((1152145853501 / 500000000000) : ℝ) = ((500000000000 / 1152145853501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (836161887 / 1000000000) ≤ -Real.log (250000000000 / 576873385013) ∧
    -Real.log (250000000000 / 576873385013) ≤ (836161889 / 1000000000) := by
  have h := checkLog_sound (w := (76873385013 / 1076873385013)) (n := 12)
    (lo := (143014707 / 1000000000)) (hi := (35753677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576873385013 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(576873385013 / 500000000000) = 1/(250000000000 / 576873385013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (836161887 / 1000000000) (836161889 / 1000000000) (Real.log (576873385013 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (576873385013 / 250000000000) = -Real.log (250000000000 / 576873385013) := by
    rw [show ((576873385013 / 250000000000) : ℝ) = ((250000000000 / 576873385013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (577650033 / 1000000000) ≤ -Real.log (500000000000 / 890923113943) ∧
    -Real.log (500000000000 / 890923113943) ≤ (288825017 / 500000000) := by
  have h := checkLog_sound (w := (390923113943 / 1390923113943)) (n := 12)
    (lo := (577650033 / 1000000000)) (hi := (288825017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((890923113943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(890923113943 / 500000000000) = 1/(500000000000 / 890923113943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (577650033 / 1000000000) (288825017 / 500000000) (Real.log (890923113943 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (890923113943 / 500000000000) = -Real.log (500000000000 / 890923113943) := by
    rw [show ((890923113943 / 500000000000) : ℝ) = ((500000000000 / 890923113943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (578570881 / 1000000000) ≤ -Real.log (62500000000 / 111467987107) ∧
    -Real.log (62500000000 / 111467987107) ≤ (289285441 / 500000000) := by
  have h := checkLog_sound (w := (48967987107 / 173967987107)) (n := 12)
    (lo := (578570881 / 1000000000)) (hi := (289285441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111467987107 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111467987107 / 62500000000) = 1/(62500000000 / 111467987107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (578570881 / 1000000000) (289285441 / 500000000) (Real.log (111467987107 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (111467987107 / 62500000000) = -Real.log (62500000000 / 111467987107) := by
    rw [show ((111467987107 / 62500000000) : ℝ) = ((62500000000 / 111467987107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (206046219 / 500000000) ≤ -Real.log (500000000000 / 754987004609) ∧
    -Real.log (500000000000 / 754987004609) ≤ (412092439 / 1000000000) := by
  have h := checkLog_sound (w := (254987004609 / 1254987004609)) (n := 12)
    (lo := (206046219 / 500000000)) (hi := (412092439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754987004609 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754987004609 / 500000000000) = 1/(500000000000 / 754987004609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (206046219 / 500000000) (412092439 / 1000000000) (Real.log (754987004609 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (754987004609 / 500000000000) = -Real.log (500000000000 / 754987004609) := by
    rw [show ((754987004609 / 500000000000) : ℝ) = ((500000000000 / 754987004609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (412762127 / 1000000000) ≤ -Real.log (500000000000 / 755492780917) ∧
    -Real.log (500000000000 / 755492780917) ≤ (25797633 / 62500000) := by
  have h := checkLog_sound (w := (255492780917 / 1255492780917)) (n := 12)
    (lo := (412762127 / 1000000000)) (hi := (25797633 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755492780917 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(755492780917 / 500000000000) = 1/(500000000000 / 755492780917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (412762127 / 1000000000) (25797633 / 62500000) (Real.log (755492780917 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (755492780917 / 500000000000) = -Real.log (500000000000 / 755492780917) := by
    rw [show ((755492780917 / 500000000000) : ℝ) = ((500000000000 / 755492780917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (42294171 / 1000000000) ≤ -Real.log (3834351 / 4000000) ∧
    -Real.log (3834351 / 4000000) ≤ (10573543 / 250000000) := by
  have h := checkLog_sound (w := (165649 / 7834351)) (n := 12)
    (lo := (42294171 / 1000000000)) (hi := (10573543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000000 / 3834351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000000 / 3834351) = 1/(3834351 / 4000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-10573543 / 250000000) (-42294171 / 1000000000) (Real.log (3834351 / 4000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (42157997 / 1000000000) ≤ -Real.log (958718293959 / 1000000000000) ∧
    -Real.log (958718293959 / 1000000000000) ≤ (21078999 / 500000000) := by
  have h := checkLog_sound (w := (41281706041 / 1958718293959)) (n := 12)
    (lo := (42157997 / 1000000000)) (hi := (21078999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958718293959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958718293959) = 1/(958718293959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-21078999 / 500000000) (-42157997 / 1000000000) (Real.log (958718293959 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell247
