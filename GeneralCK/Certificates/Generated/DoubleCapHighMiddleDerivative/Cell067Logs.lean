import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell067
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

theorem reflection_log_1_neg : (254521087 / 1000000000) ≤ -Real.log (1280 / 1651) ∧
    -Real.log (1280 / 1651) ≤ (994223 / 3906250) := by
  have h := checkLog_sound (w := (371 / 2931)) (n := 12)
    (lo := (254521087 / 1000000000)) (hi := (994223 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1651 / 1280) = 1/(1280 / 1651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (254521087 / 1000000000) (994223 / 3906250) (Real.log (1651 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1651 / 1280) = -Real.log (1280 / 1651) := by
    rw [show ((1651 / 1280) : ℝ) = ((1280 / 1651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (171135131 / 500000000) ≤ -Real.log (909 / 1280) ∧
    -Real.log (909 / 1280) ≤ (342270263 / 1000000000) := by
  have h := checkLog_sound (w := (371 / 2189)) (n := 12)
    (lo := (171135131 / 500000000)) (hi := (342270263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 909) = 1/(909 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-342270263 / 1000000000) (-171135131 / 500000000) (Real.log (909 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (254066713 / 1000000000) ≤ -Real.log (5120 / 6601) ∧
    -Real.log (5120 / 6601) ≤ (127033357 / 500000000) := by
  have h := checkLog_sound (w := (1481 / 11721)) (n := 12)
    (lo := (254066713 / 1000000000)) (hi := (127033357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6601 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6601 / 5120) = 1/(5120 / 6601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (254066713 / 1000000000) (127033357 / 500000000) (Real.log (6601 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6601 / 5120) = -Real.log (5120 / 6601) := by
    rw [show ((6601 / 5120) : ℝ) = ((5120 / 6601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (4268069 / 12500000) ≤ -Real.log (3639 / 5120) ∧
    -Real.log (3639 / 5120) ≤ (341445521 / 1000000000) := by
  have h := checkLog_sound (w := (1481 / 8759)) (n := 12)
    (lo := (4268069 / 12500000)) (hi := (341445521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3639) = 1/(3639 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-341445521 / 1000000000) (-4268069 / 12500000) (Real.log (3639 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (46676939 / 250000000) ≤ -Real.log (40000 / 48211) ∧
    -Real.log (40000 / 48211) ≤ (186707757 / 1000000000) := by
  have h := checkLog_sound (w := (8211 / 88211)) (n := 12)
    (lo := (46676939 / 250000000)) (hi := (186707757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48211 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48211 / 40000) = 1/(40000 / 48211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (46676939 / 250000000) (186707757 / 1000000000) (Real.log (48211 / 40000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (48211 / 40000) = -Real.log (40000 / 48211) := by
    rw [show ((48211 / 40000) : ℝ) = ((40000 / 48211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (7179973 / 31250000) ≤ -Real.log (31789 / 40000) ∧
    -Real.log (31789 / 40000) ≤ (229759137 / 1000000000) := by
  have h := checkLog_sound (w := (8211 / 71789)) (n := 12)
    (lo := (7179973 / 31250000)) (hi := (229759137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31789) = 1/(31789 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-229759137 / 1000000000) (-7179973 / 31250000) (Real.log (31789 / 40000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (93527667 / 500000000) ≤ -Real.log (500000 / 602847) ∧
    -Real.log (500000 / 602847) ≤ (37411067 / 200000000) := by
  have h := checkLog_sound (w := (102847 / 1102847)) (n := 12)
    (lo := (93527667 / 500000000)) (hi := (37411067 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602847 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602847 / 500000) = 1/(500000 / 602847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (93527667 / 500000000) (37411067 / 200000000) (Real.log (602847 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (602847 / 500000) = -Real.log (500000 / 602847) := by
    rw [show ((602847 / 500000) : ℝ) = ((500000 / 602847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (230286501 / 1000000000) ≤ -Real.log (397153 / 500000) ∧
    -Real.log (397153 / 500000) ≤ (115143251 / 500000000) := by
  have h := checkLog_sound (w := (102847 / 897153)) (n := 12)
    (lo := (230286501 / 1000000000)) (hi := (115143251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 397153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 397153) = 1/(397153 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-115143251 / 500000000) (-230286501 / 1000000000) (Real.log (397153 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (34258251 / 250000000) ≤ -Real.log (500000 / 573433) ∧
    -Real.log (500000 / 573433) ≤ (27406601 / 200000000) := by
  have h := checkLog_sound (w := (73433 / 1073433)) (n := 12)
    (lo := (34258251 / 250000000)) (hi := (27406601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((573433 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(573433 / 500000) = 1/(500000 / 573433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (34258251 / 250000000) (27406601 / 200000000) (Real.log (573433 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (573433 / 500000) = -Real.log (500000 / 573433) := by
    rw [show ((573433 / 500000) : ℝ) = ((500000 / 573433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (158838651 / 1000000000) ≤ -Real.log (426567 / 500000) ∧
    -Real.log (426567 / 500000) ≤ (39709663 / 250000000) := by
  have h := checkLog_sound (w := (73433 / 926567)) (n := 12)
    (lo := (158838651 / 1000000000)) (hi := (39709663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 426567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 426567) = 1/(426567 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-39709663 / 250000000) (-158838651 / 1000000000) (Real.log (426567 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (68650763 / 500000000) ≤ -Real.log (500000 / 573587) ∧
    -Real.log (500000 / 573587) ≤ (137301527 / 1000000000) := by
  have h := checkLog_sound (w := (73587 / 1073587)) (n := 12)
    (lo := (68650763 / 500000000)) (hi := (137301527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((573587 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(573587 / 500000) = 1/(500000 / 573587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (68650763 / 500000000) (137301527 / 1000000000) (Real.log (573587 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (573587 / 500000) = -Real.log (500000 / 573587) := by
    rw [show ((573587 / 500000) : ℝ) = ((500000 / 573587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (79599869 / 500000000) ≤ -Real.log (426413 / 500000) ∧
    -Real.log (426413 / 500000) ≤ (159199739 / 1000000000) := by
  have h := checkLog_sound (w := (73587 / 926413)) (n := 12)
    (lo := (79599869 / 500000000)) (hi := (159199739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 426413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 426413) = 1/(426413 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-159199739 / 1000000000) (-79599869 / 500000000) (Real.log (426413 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (297756117 / 500000000) ≤ -Real.log (500000000000 / 906979939543) ∧
    -Real.log (500000000000 / 906979939543) ≤ (119102447 / 200000000) := by
  have h := checkLog_sound (w := (406979939543 / 1406979939543)) (n := 12)
    (lo := (297756117 / 500000000)) (hi := (119102447 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((906979939543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(906979939543 / 500000000000) = 1/(500000000000 / 906979939543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (297756117 / 500000000) (119102447 / 200000000) (Real.log (906979939543 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (906979939543 / 500000000000) = -Real.log (500000000000 / 906979939543) := by
    rw [show ((906979939543 / 500000000000) : ℝ) = ((500000000000 / 906979939543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (596791349 / 1000000000) ≤ -Real.log (250000000000 / 454070407041) ∧
    -Real.log (250000000000 / 454070407041) ≤ (11935827 / 20000000) := by
  have h := checkLog_sound (w := (204070407041 / 704070407041)) (n := 12)
    (lo := (596791349 / 1000000000)) (hi := (11935827 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((454070407041 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(454070407041 / 250000000000) = 1/(250000000000 / 454070407041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (596791349 / 1000000000) (11935827 / 20000000) (Real.log (454070407041 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (454070407041 / 250000000000) = -Real.log (250000000000 / 454070407041) := by
    rw [show ((454070407041 / 250000000000) : ℝ) = ((250000000000 / 454070407041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (104116723 / 250000000) ≤ -Real.log (31250000000 / 47393555947) ∧
    -Real.log (31250000000 / 47393555947) ≤ (416466893 / 1000000000) := by
  have h := checkLog_sound (w := (16143555947 / 78643555947)) (n := 12)
    (lo := (104116723 / 250000000)) (hi := (416466893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47393555947 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47393555947 / 31250000000) = 1/(31250000000 / 47393555947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (104116723 / 250000000) (416466893 / 1000000000) (Real.log (47393555947 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (47393555947 / 31250000000) = -Real.log (31250000000 / 47393555947) := by
    rw [show ((47393555947 / 31250000000) : ℝ) = ((31250000000 / 47393555947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (104335459 / 250000000) ≤ -Real.log (125000000000 / 189740163111) ∧
    -Real.log (125000000000 / 189740163111) ≤ (417341837 / 1000000000) := by
  have h := checkLog_sound (w := (64740163111 / 314740163111)) (n := 12)
    (lo := (104335459 / 250000000)) (hi := (417341837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189740163111 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189740163111 / 125000000000) = 1/(125000000000 / 189740163111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (104335459 / 250000000) (417341837 / 1000000000) (Real.log (189740163111 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (189740163111 / 125000000000) = -Real.log (125000000000 / 189740163111) := by
    rw [show ((189740163111 / 125000000000) : ℝ) = ((125000000000 / 189740163111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (36983957 / 125000000) ≤ -Real.log (100000000000 / 134429761327) ∧
    -Real.log (100000000000 / 134429761327) ≤ (295871657 / 1000000000) := by
  have h := checkLog_sound (w := (34429761327 / 234429761327)) (n := 12)
    (lo := (36983957 / 125000000)) (hi := (295871657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134429761327 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134429761327 / 100000000000) = 1/(100000000000 / 134429761327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (36983957 / 125000000) (295871657 / 1000000000) (Real.log (134429761327 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (134429761327 / 100000000000) = -Real.log (100000000000 / 134429761327) := by
    rw [show ((134429761327 / 100000000000) : ℝ) = ((100000000000 / 134429761327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (18531329 / 62500000) ≤ -Real.log (20000000000 / 26902885231) ∧
    -Real.log (20000000000 / 26902885231) ≤ (59300253 / 200000000) := by
  have h := checkLog_sound (w := (6902885231 / 46902885231)) (n := 12)
    (lo := (18531329 / 62500000)) (hi := (59300253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26902885231 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26902885231 / 20000000000) = 1/(20000000000 / 26902885231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (18531329 / 62500000) (59300253 / 200000000) (Real.log (26902885231 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (26902885231 / 20000000000) = -Real.log (20000000000 / 26902885231) := by
    rw [show ((26902885231 / 20000000000) : ℝ) = ((20000000000 / 26902885231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21898211 / 1000000000) ≤ -Real.log (244584953431 / 250000000000) ∧
    -Real.log (244584953431 / 250000000000) ≤ (5474553 / 250000000) := by
  have h := checkLog_sound (w := (5415046569 / 494584953431)) (n := 12)
    (lo := (21898211 / 1000000000)) (hi := (5474553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244584953431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244584953431) = 1/(244584953431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5474553 / 250000000) (-21898211 / 1000000000) (Real.log (244584953431 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (10902823 / 500000000) ≤ -Real.log (244607594511 / 250000000000) ∧
    -Real.log (244607594511 / 250000000000) ≤ (21805647 / 1000000000) := by
  have h := checkLog_sound (w := (5392405489 / 494607594511)) (n := 12)
    (lo := (10902823 / 500000000)) (hi := (21805647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244607594511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244607594511) = 1/(244607594511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-21805647 / 1000000000) (-10902823 / 500000000) (Real.log (244607594511 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell067
