import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell175
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

theorem reflection_log_1_neg : (75604183 / 250000000) ≤ -Real.log (320 / 433) ∧
    -Real.log (320 / 433) ≤ (302416733 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 753)) (n := 12)
    (lo := (75604183 / 250000000)) (hi := (302416733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(433 / 320) = 1/(320 / 433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (75604183 / 250000000) (302416733 / 1000000000) (Real.log (433 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (433 / 320) = -Real.log (320 / 433) := by
    rw [show ((433 / 320) : ℝ) = ((320 / 433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (217801101 / 500000000) ≤ -Real.log (207 / 320) ∧
    -Real.log (207 / 320) ≤ (435602203 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 207) = 1/(207 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-435602203 / 1000000000) (-217801101 / 500000000) (Real.log (207 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (301983613 / 1000000000) ≤ -Real.log (1024 / 1385) ∧
    -Real.log (1024 / 1385) ≤ (150991807 / 500000000) := by
  have h := checkLog_sound (w := (361 / 2409)) (n := 12)
    (lo := (301983613 / 1000000000)) (hi := (150991807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1385 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1385 / 1024) = 1/(1024 / 1385) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (301983613 / 1000000000) (150991807 / 500000000) (Real.log (1385 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1385 / 1024) = -Real.log (1024 / 1385) := by
    rw [show ((1385 / 1024) : ℝ) = ((1024 / 1385) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (86939363 / 200000000) ≤ -Real.log (663 / 1024) ∧
    -Real.log (663 / 1024) ≤ (27168551 / 62500000) := by
  have h := checkLog_sound (w := (361 / 1687)) (n := 12)
    (lo := (86939363 / 200000000)) (hi := (27168551 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 663) = 1/(663 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-27168551 / 62500000) (-86939363 / 200000000) (Real.log (663 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (111829309 / 500000000) ≤ -Real.log (250000 / 312661) ∧
    -Real.log (250000 / 312661) ≤ (223658619 / 1000000000) := by
  have h := checkLog_sound (w := (62661 / 562661)) (n := 12)
    (lo := (111829309 / 500000000)) (hi := (223658619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((312661 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(312661 / 250000) = 1/(250000 / 312661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (111829309 / 500000000) (223658619 / 1000000000) (Real.log (312661 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (312661 / 250000) = -Real.log (250000 / 312661) := by
    rw [show ((312661 / 250000) : ℝ) = ((250000 / 312661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (288541107 / 1000000000) ≤ -Real.log (187339 / 250000) ∧
    -Real.log (187339 / 250000) ≤ (72135277 / 250000000) := by
  have h := checkLog_sound (w := (62661 / 437339)) (n := 12)
    (lo := (288541107 / 1000000000)) (hi := (72135277 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 187339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 187339) = 1/(187339 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-72135277 / 250000000) (-288541107 / 1000000000) (Real.log (187339 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (223996787 / 1000000000) ≤ -Real.log (1000000 / 1251067) ∧
    -Real.log (1000000 / 1251067) ≤ (55999197 / 250000000) := by
  have h := checkLog_sound (w := (251067 / 2251067)) (n := 12)
    (lo := (223996787 / 1000000000)) (hi := (55999197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251067 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251067 / 1000000) = 1/(1000000 / 1251067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (223996787 / 1000000000) (55999197 / 250000000) (Real.log (1251067 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1251067 / 1000000) = -Real.log (1000000 / 1251067) := by
    rw [show ((1251067 / 1000000) : ℝ) = ((1000000 / 1251067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (36138219 / 125000000) ≤ -Real.log (748933 / 1000000) ∧
    -Real.log (748933 / 1000000) ≤ (289105753 / 1000000000) := by
  have h := checkLog_sound (w := (251067 / 1748933)) (n := 12)
    (lo := (36138219 / 125000000)) (hi := (289105753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 748933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 748933) = 1/(748933 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-289105753 / 1000000000) (-36138219 / 125000000) (Real.log (748933 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (33165759 / 200000000) ≤ -Real.log (1000000 / 1180371) ∧
    -Real.log (1000000 / 1180371) ≤ (41457199 / 250000000) := by
  have h := checkLog_sound (w := (180371 / 2180371)) (n := 12)
    (lo := (33165759 / 200000000)) (hi := (41457199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1180371 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1180371 / 1000000) = 1/(1000000 / 1180371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (33165759 / 200000000) (41457199 / 250000000) (Real.log (1180371 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1180371 / 1000000) = -Real.log (1000000 / 1180371) := by
    rw [show ((1180371 / 1000000) : ℝ) = ((1000000 / 1180371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4972587 / 25000000) ≤ -Real.log (819629 / 1000000) ∧
    -Real.log (819629 / 1000000) ≤ (198903481 / 1000000000) := by
  have h := checkLog_sound (w := (180371 / 1819629)) (n := 12)
    (lo := (4972587 / 25000000)) (hi := (198903481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 819629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 819629) = 1/(819629 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-198903481 / 1000000000) (-4972587 / 25000000) (Real.log (819629 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (265753 / 1600000) ≤ -Real.log (500000 / 590343) ∧
    -Real.log (500000 / 590343) ≤ (83047813 / 500000000) := by
  have h := checkLog_sound (w := (90343 / 1090343)) (n := 12)
    (lo := (265753 / 1600000)) (hi := (83047813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590343 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590343 / 500000) = 1/(500000 / 590343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (265753 / 1600000) (83047813 / 500000000) (Real.log (590343 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (590343 / 500000) = -Real.log (500000 / 590343) := by
    rw [show ((590343 / 500000) : ℝ) = ((500000 / 590343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (99643937 / 500000000) ≤ -Real.log (409657 / 500000) ∧
    -Real.log (409657 / 500000) ≤ (1594303 / 8000000) := by
  have h := checkLog_sound (w := (90343 / 909657)) (n := 12)
    (lo := (99643937 / 500000000)) (hi := (1594303 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409657) = 1/(409657 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1594303 / 8000000) (-99643937 / 500000000) (Real.log (409657 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (736680427 / 1000000000) ≤ -Real.log (100000000000 / 208898944193) ∧
    -Real.log (100000000000 / 208898944193) ≤ (736680429 / 1000000000) := by
  have h := checkLog_sound (w := (8898944193 / 408898944193)) (n := 12)
    (lo := (43533247 / 1000000000)) (hi := (680207 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((208898944193 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(208898944193 / 200000000000) = 1/(100000000000 / 208898944193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (736680427 / 1000000000) (736680429 / 1000000000) (Real.log (208898944193 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (208898944193 / 100000000000) = -Real.log (100000000000 / 208898944193) := by
    rw [show ((208898944193 / 100000000000) : ℝ) = ((100000000000 / 208898944193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (369009467 / 500000000) ≤ -Real.log (500000000000 / 1045893719807) ∧
    -Real.log (500000000000 / 1045893719807) ≤ (92252367 / 125000000) := by
  have h := checkLog_sound (w := (45893719807 / 2045893719807)) (n := 12)
    (lo := (22435877 / 500000000)) (hi := (8974351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1045893719807 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1045893719807 / 1000000000000) = 1/(500000000000 / 1045893719807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (369009467 / 500000000) (92252367 / 125000000) (Real.log (1045893719807 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1045893719807 / 500000000000) = -Real.log (500000000000 / 1045893719807) := by
    rw [show ((1045893719807 / 500000000000) : ℝ) = ((500000000000 / 1045893719807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (256099863 / 500000000) ≤ -Real.log (100000000000 / 166895841229) ∧
    -Real.log (100000000000 / 166895841229) ≤ (512199727 / 1000000000) := by
  have h := checkLog_sound (w := (66895841229 / 266895841229)) (n := 12)
    (lo := (256099863 / 500000000)) (hi := (512199727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166895841229 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166895841229 / 100000000000) = 1/(100000000000 / 166895841229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (256099863 / 500000000) (512199727 / 1000000000) (Real.log (166895841229 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (166895841229 / 100000000000) = -Real.log (100000000000 / 166895841229) := by
    rw [show ((166895841229 / 100000000000) : ℝ) = ((100000000000 / 166895841229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (513102539 / 1000000000) ≤ -Real.log (125000000000 / 208808231177) ∧
    -Real.log (125000000000 / 208808231177) ≤ (25655127 / 50000000) := by
  have h := checkLog_sound (w := (83808231177 / 333808231177)) (n := 12)
    (lo := (513102539 / 1000000000)) (hi := (25655127 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((208808231177 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(208808231177 / 125000000000) = 1/(125000000000 / 208808231177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (513102539 / 1000000000) (25655127 / 50000000) (Real.log (208808231177 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (208808231177 / 125000000000) = -Real.log (125000000000 / 208808231177) := by
    rw [show ((208808231177 / 125000000000) : ℝ) = ((125000000000 / 208808231177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (14589291 / 40000000) ≤ -Real.log (250000000000 / 360032099889) ∧
    -Real.log (250000000000 / 360032099889) ≤ (91183069 / 250000000) := by
  have h := checkLog_sound (w := (110032099889 / 610032099889)) (n := 12)
    (lo := (14589291 / 40000000)) (hi := (91183069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360032099889 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360032099889 / 250000000000) = 1/(250000000000 / 360032099889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (14589291 / 40000000) (91183069 / 250000000) (Real.log (360032099889 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (360032099889 / 250000000000) = -Real.log (250000000000 / 360032099889) := by
    rw [show ((360032099889 / 250000000000) : ℝ) = ((250000000000 / 360032099889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (365383499 / 1000000000) ≤ -Real.log (500000000000 / 720533275399) ∧
    -Real.log (500000000000 / 720533275399) ≤ (730767 / 2000000) := by
  have h := checkLog_sound (w := (220533275399 / 1220533275399)) (n := 12)
    (lo := (365383499 / 1000000000)) (hi := (730767 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720533275399 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720533275399 / 500000000000) = 1/(500000000000 / 720533275399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (365383499 / 1000000000) (730767 / 2000000) (Real.log (720533275399 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (720533275399 / 500000000000) = -Real.log (500000000000 / 720533275399) := by
    rw [show ((720533275399 / 500000000000) : ℝ) = ((500000000000 / 720533275399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4149031 / 125000000) ≤ -Real.log (241838142351 / 250000000000) ∧
    -Real.log (241838142351 / 250000000000) ≤ (33192249 / 1000000000) := by
  have h := checkLog_sound (w := (8161857649 / 491838142351)) (n := 12)
    (lo := (4149031 / 125000000)) (hi := (33192249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241838142351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241838142351) = 1/(241838142351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-33192249 / 1000000000) (-4149031 / 125000000) (Real.log (241838142351 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8268671 / 250000000) ≤ -Real.log (967466302359 / 1000000000000) ∧
    -Real.log (967466302359 / 1000000000000) ≤ (6614937 / 200000000) := by
  have h := checkLog_sound (w := (32533697641 / 1967466302359)) (n := 12)
    (lo := (8268671 / 250000000)) (hi := (6614937 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967466302359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967466302359) = 1/(967466302359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6614937 / 200000000) (-8268671 / 250000000) (Real.log (967466302359 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell175
