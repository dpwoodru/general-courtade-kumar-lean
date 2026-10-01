import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13056_neg : (7450861 / 15625000) ≤ -Real.log (1000 / 1611) ∧
    -Real.log (1000 / 1611) ≤ (95371021 / 200000000) := by
  have h := checkLog_sound (w := (611 / 2611)) (n := 12)
    (lo := (7450861 / 15625000)) (hi := (95371021 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1611 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1611 / 1000) = 1/(1000 / 1611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13056 : Bounds (7450861 / 15625000) (95371021 / 200000000) (Real.log (1611 / 1000)) := by
  have h := reflection_log_13056_neg
  have he : Real.log (1611 / 1000) = -Real.log (1000 / 1611) := by
    rw [show ((1611 / 1000) : ℝ) = ((1000 / 1611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13057_neg : (472087967 / 500000000) ≤ -Real.log (389 / 1000) ∧
    -Real.log (389 / 1000) ≤ (14752749 / 15625000) := by
  have h := checkLog_sound (w := (111 / 889)) (n := 12)
    (lo := (125514377 / 500000000)) (hi := (50205751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 389) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 389) = 1/(389 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13057 : Bounds (-14752749 / 15625000) (-472087967 / 500000000) (Real.log (389 / 1000)) := by
  have h := reflection_log_13057_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13058_neg : (610813 / 1000000000) ≤ -Real.log (1000000 / 1000611) ∧
    -Real.log (1000000 / 1000611) ≤ (305407 / 500000000) := by
  have h := checkLog_sound (w := (611 / 2000611)) (n := 12)
    (lo := (610813 / 1000000000)) (hi := (305407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000611 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000611 / 1000000) = 1/(1000000 / 1000611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13058 : Bounds (610813 / 1000000000) (305407 / 500000000) (Real.log (1000611 / 1000000)) := by
  have h := reflection_log_13058_neg
  have he : Real.log (1000611 / 1000000) = -Real.log (1000000 / 1000611) := by
    rw [show ((1000611 / 1000000) : ℝ) = ((1000000 / 1000611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13059_neg : (305593 / 500000000) ≤ -Real.log (999389 / 1000000) ∧
    -Real.log (999389 / 1000000) ≤ (611187 / 1000000000) := by
  have h := checkLog_sound (w := (611 / 1999389)) (n := 12)
    (lo := (305593 / 500000000)) (hi := (611187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999389) = 1/(999389 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13059 : Bounds (-611187 / 1000000000) (-305593 / 500000000) (Real.log (999389 / 1000000)) := by
  have h := reflection_log_13059_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13060_neg : (282635107 / 1000000000) ≤ -Real.log (1000000 / 1326621) ∧
    -Real.log (1000000 / 1326621) ≤ (70658777 / 250000000) := by
  have h := checkLog_sound (w := (326621 / 2326621)) (n := 12)
    (lo := (282635107 / 1000000000)) (hi := (70658777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1326621 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1326621 / 1000000) = 1/(1000000 / 1326621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13060 : Bounds (282635107 / 1000000000) (70658777 / 250000000) (Real.log (1326621 / 1000000)) := by
  have h := reflection_log_13060_neg
  have he : Real.log (1326621 / 1000000) = -Real.log (1000000 / 1326621) := by
    rw [show ((1326621 / 1000000) : ℝ) = ((1000000 / 1326621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13061_neg : (395446957 / 1000000000) ≤ -Real.log (673379 / 1000000) ∧
    -Real.log (673379 / 1000000) ≤ (197723479 / 500000000) := by
  have h := checkLog_sound (w := (326621 / 1673379)) (n := 12)
    (lo := (395446957 / 1000000000)) (hi := (197723479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 673379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 673379) = 1/(673379 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13061 : Bounds (-197723479 / 500000000) (-395446957 / 1000000000) (Real.log (673379 / 1000000)) := by
  have h := reflection_log_13061_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13062_neg : (142233329 / 500000000) ≤ -Real.log (1000000 / 1329053) ∧
    -Real.log (1000000 / 1329053) ≤ (284466659 / 1000000000) := by
  have h := checkLog_sound (w := (329053 / 2329053)) (n := 12)
    (lo := (142233329 / 500000000)) (hi := (284466659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1329053 / 1000000) = 1/(1000000 / 1329053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13062 : Bounds (142233329 / 500000000) (284466659 / 1000000000) (Real.log (1329053 / 1000000)) := by
  have h := reflection_log_13062_neg
  have he : Real.log (1329053 / 1000000) = -Real.log (1000000 / 1329053) := by
    rw [show ((1329053 / 1000000) : ℝ) = ((1000000 / 1329053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13063_neg : (399065131 / 1000000000) ≤ -Real.log (670947 / 1000000) ∧
    -Real.log (670947 / 1000000) ≤ (99766283 / 250000000) := by
  have h := checkLog_sound (w := (329053 / 1670947)) (n := 12)
    (lo := (399065131 / 1000000000)) (hi := (99766283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 670947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 670947) = 1/(670947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13063 : Bounds (-99766283 / 250000000) (-399065131 / 1000000000) (Real.log (670947 / 1000000)) := by
  have h := reflection_log_13063_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13064_neg : (114598473 / 1000000000) ≤ -Real.log (891724123191 / 1000000000000) ∧
    -Real.log (891724123191 / 1000000000000) ≤ (57299237 / 500000000) := by
  have h := checkLog_sound (w := (108275876809 / 1891724123191)) (n := 12)
    (lo := (114598473 / 1000000000)) (hi := (57299237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 891724123191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 891724123191) = 1/(891724123191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13064 : Bounds (-57299237 / 500000000) (-114598473 / 1000000000) (Real.log (891724123191 / 1000000000000)) := by
  have h := reflection_log_13064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13065_neg : (112811849 / 1000000000) ≤ -Real.log (893318722359 / 1000000000000) ∧
    -Real.log (893318722359 / 1000000000000) ≤ (2256237 / 20000000) := by
  have h := checkLog_sound (w := (106681277641 / 1893318722359)) (n := 12)
    (lo := (112811849 / 1000000000)) (hi := (2256237 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 893318722359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 893318722359) = 1/(893318722359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13065 : Bounds (-2256237 / 20000000) (-112811849 / 1000000000) (Real.log (893318722359 / 1000000000000)) := by
  have h := reflection_log_13065_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13066_neg : (135616413 / 200000000) ≤ -Real.log (500000000000 / 985047796263) ∧
    -Real.log (500000000000 / 985047796263) ≤ (339041033 / 500000000) := by
  have h := checkLog_sound (w := (485047796263 / 1485047796263)) (n := 12)
    (lo := (135616413 / 200000000)) (hi := (339041033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((985047796263 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(985047796263 / 500000000000) = 1/(500000000000 / 985047796263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13066 : Bounds (135616413 / 200000000) (339041033 / 500000000) (Real.log (985047796263 / 500000000000)) := by
  have h := reflection_log_13066_neg
  have he : Real.log (985047796263 / 500000000000) = -Real.log (500000000000 / 985047796263) := by
    rw [show ((985047796263 / 500000000000) : ℝ) = ((500000000000 / 985047796263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13067_neg : (68353179 / 100000000) ≤ -Real.log (500000000000 / 990430689757) ∧
    -Real.log (500000000000 / 990430689757) ≤ (683531791 / 1000000000) := by
  have h := checkLog_sound (w := (490430689757 / 1490430689757)) (n := 12)
    (lo := (68353179 / 100000000)) (hi := (683531791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990430689757 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990430689757 / 500000000000) = 1/(500000000000 / 990430689757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13067 : Bounds (68353179 / 100000000) (683531791 / 1000000000) (Real.log (990430689757 / 500000000000)) := by
  have h := reflection_log_13067_neg
  have he : Real.log (990430689757 / 500000000000) = -Real.log (500000000000 / 990430689757) := by
    rw [show ((990430689757 / 500000000000) : ℝ) = ((500000000000 / 990430689757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13068_neg : (22054447 / 15625000) ≤ -Real.log (500000000000 / 2051020408163) ∧
    -Real.log (500000000000 / 2051020408163) ≤ (1411484611 / 1000000000) := by
  have h := checkLog_sound (w := (51020408163 / 4051020408163)) (n := 12)
    (lo := (3148781 / 125000000)) (hi := (25190249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2051020408163 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2051020408163 / 2000000000000) = 1/(500000000000 / 2051020408163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13068 : Bounds (22054447 / 15625000) (1411484611 / 1000000000) (Real.log (2051020408163 / 500000000000)) := by
  have h := reflection_log_13068_neg
  have he : Real.log (2051020408163 / 500000000000) = -Real.log (500000000000 / 2051020408163) := by
    rw [show ((2051020408163 / 500000000000) : ℝ) = ((500000000000 / 2051020408163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13069_neg : (710515519 / 500000000) ≤ -Real.log (125000000000 / 517673521851) ∧
    -Real.log (125000000000 / 517673521851) ≤ (1421031041 / 1000000000) := by
  have h := checkLog_sound (w := (17673521851 / 1017673521851)) (n := 12)
    (lo := (17368339 / 500000000)) (hi := (34736679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517673521851 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(517673521851 / 500000000000) = 1/(125000000000 / 517673521851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13069 : Bounds (710515519 / 500000000) (1421031041 / 1000000000) (Real.log (517673521851 / 125000000000)) := by
  have h := reflection_log_13069_neg
  have he : Real.log (517673521851 / 125000000000) = -Real.log (125000000000 / 517673521851) := by
    rw [show ((517673521851 / 125000000000) : ℝ) = ((125000000000 / 517673521851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13070_neg : (478715569 / 1000000000) ≤ -Real.log (500 / 807) ∧
    -Real.log (500 / 807) ≤ (47871557 / 100000000) := by
  have h := checkLog_sound (w := (307 / 1307)) (n := 12)
    (lo := (478715569 / 1000000000)) (hi := (47871557 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(807 / 500) = 1/(500 / 807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13070 : Bounds (478715569 / 1000000000) (47871557 / 100000000) (Real.log (807 / 500)) := by
  have h := reflection_log_13070_neg
  have he : Real.log (807 / 500) = -Real.log (500 / 807) := by
    rw [show ((807 / 500) : ℝ) = ((500 / 807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13071_neg : (237979477 / 250000000) ≤ -Real.log (193 / 500) ∧
    -Real.log (193 / 500) ≤ (95191791 / 100000000) := by
  have h := checkLog_sound (w := (57 / 443)) (n := 12)
    (lo := (32346341 / 125000000)) (hi := (258770729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 193) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 193) = 1/(193 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13071 : Bounds (-95191791 / 100000000) (-237979477 / 250000000) (Real.log (193 / 500)) := by
  have h := reflection_log_13071_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13072_neg : (613811 / 1000000000) ≤ -Real.log (500000 / 500307) ∧
    -Real.log (500000 / 500307) ≤ (153453 / 250000000) := by
  have h := checkLog_sound (w := (307 / 1000307)) (n := 12)
    (lo := (613811 / 1000000000)) (hi := (153453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500307 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500307 / 500000) = 1/(500000 / 500307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13072 : Bounds (613811 / 1000000000) (153453 / 250000000) (Real.log (500307 / 500000)) := by
  have h := reflection_log_13072_neg
  have he : Real.log (500307 / 500000) = -Real.log (500000 / 500307) := by
    rw [show ((500307 / 500000) : ℝ) = ((500000 / 500307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13073_neg : (153547 / 250000000) ≤ -Real.log (499693 / 500000) ∧
    -Real.log (499693 / 500000) ≤ (614189 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 999693)) (n := 12)
    (lo := (153547 / 250000000)) (hi := (614189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499693) = 1/(499693 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13073 : Bounds (-614189 / 1000000000) (-153547 / 250000000) (Real.log (499693 / 500000)) := by
  have h := reflection_log_13073_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13074_neg : (284045217 / 1000000000) ≤ -Real.log (1000000 / 1328493) ∧
    -Real.log (1000000 / 1328493) ≤ (142022609 / 500000000) := by
  have h := checkLog_sound (w := (328493 / 2328493)) (n := 12)
    (lo := (284045217 / 1000000000)) (hi := (142022609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1328493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1328493 / 1000000) = 1/(1000000 / 1328493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13074 : Bounds (284045217 / 1000000000) (142022609 / 500000000) (Real.log (1328493 / 1000000)) := by
  have h := reflection_log_13074_neg
  have he : Real.log (1328493 / 1000000) = -Real.log (1000000 / 1328493) := by
    rw [show ((1328493 / 1000000) : ℝ) = ((1000000 / 1328493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13075_neg : (199115419 / 500000000) ≤ -Real.log (671507 / 1000000) ∧
    -Real.log (671507 / 1000000) ≤ (398230839 / 1000000000) := by
  have h := checkLog_sound (w := (328493 / 1671507)) (n := 12)
    (lo := (199115419 / 500000000)) (hi := (398230839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 671507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 671507) = 1/(671507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13075 : Bounds (-398230839 / 1000000000) (-199115419 / 500000000) (Real.log (671507 / 1000000)) := by
  have h := reflection_log_13075_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13076_neg : (35734931 / 125000000) ≤ -Real.log (250000 / 332733) ∧
    -Real.log (250000 / 332733) ≤ (285879449 / 1000000000) := by
  have h := checkLog_sound (w := (82733 / 582733)) (n := 12)
    (lo := (35734931 / 125000000)) (hi := (285879449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332733 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(332733 / 250000) = 1/(250000 / 332733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13076 : Bounds (35734931 / 125000000) (285879449 / 1000000000) (Real.log (332733 / 250000)) := by
  have h := reflection_log_13076_neg
  have he : Real.log (332733 / 250000) = -Real.log (250000 / 332733) := by
    rw [show ((332733 / 250000) : ℝ) = ((250000 / 332733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13077_neg : (401869579 / 1000000000) ≤ -Real.log (167267 / 250000) ∧
    -Real.log (167267 / 250000) ≤ (20093479 / 50000000) := by
  have h := checkLog_sound (w := (82733 / 417267)) (n := 12)
    (lo := (401869579 / 1000000000)) (hi := (20093479 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 167267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 167267) = 1/(167267 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13077 : Bounds (-20093479 / 50000000) (-401869579 / 1000000000) (Real.log (167267 / 250000)) := by
  have h := reflection_log_13077_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13078_neg : (115990131 / 1000000000) ≤ -Real.log (55655250711 / 62500000000) ∧
    -Real.log (55655250711 / 62500000000) ≤ (28997533 / 250000000) := by
  have h := checkLog_sound (w := (6844749289 / 118155250711)) (n := 12)
    (lo := (115990131 / 1000000000)) (hi := (28997533 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 55655250711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 55655250711) = 1/(55655250711 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13078 : Bounds (-28997533 / 250000000) (-115990131 / 1000000000) (Real.log (55655250711 / 62500000000)) := by
  have h := reflection_log_13078_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13079_neg : (114185621 / 1000000000) ≤ -Real.log (892092348951 / 1000000000000) ∧
    -Real.log (892092348951 / 1000000000000) ≤ (57092811 / 500000000) := by
  have h := checkLog_sound (w := (107907651049 / 1892092348951)) (n := 12)
    (lo := (114185621 / 1000000000)) (hi := (57092811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 892092348951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 892092348951) = 1/(892092348951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13079 : Bounds (-57092811 / 500000000) (-114185621 / 1000000000) (Real.log (892092348951 / 1000000000000)) := by
  have h := reflection_log_13079_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13080_neg : (136455211 / 200000000) ≤ -Real.log (125000000000 / 247296938081) ∧
    -Real.log (125000000000 / 247296938081) ≤ (85284507 / 125000000) := by
  have h := checkLog_sound (w := (122296938081 / 372296938081)) (n := 12)
    (lo := (136455211 / 200000000)) (hi := (85284507 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247296938081 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247296938081 / 125000000000) = 1/(125000000000 / 247296938081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13080 : Bounds (136455211 / 200000000) (85284507 / 125000000) (Real.log (247296938081 / 125000000000)) := by
  have h := reflection_log_13080_neg
  have he : Real.log (247296938081 / 125000000000) = -Real.log (125000000000 / 247296938081) := by
    rw [show ((247296938081 / 125000000000) : ℝ) = ((125000000000 / 247296938081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13081_neg : (171937257 / 250000000) ≤ -Real.log (500000000000 / 994616391757) ∧
    -Real.log (500000000000 / 994616391757) ≤ (687749029 / 1000000000) := by
  have h := checkLog_sound (w := (494616391757 / 1494616391757)) (n := 12)
    (lo := (171937257 / 250000000)) (hi := (687749029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((994616391757 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(994616391757 / 500000000000) = 1/(500000000000 / 994616391757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13081 : Bounds (171937257 / 250000000) (687749029 / 1000000000) (Real.log (994616391757 / 500000000000)) := by
  have h := reflection_log_13081_neg
  have he : Real.log (994616391757 / 500000000000) = -Real.log (500000000000 / 994616391757) := by
    rw [show ((994616391757 / 500000000000) : ℝ) = ((500000000000 / 994616391757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13082_neg : (710515519 / 500000000) ≤ -Real.log (500000000000 / 2070694087403) ∧
    -Real.log (500000000000 / 2070694087403) ≤ (1421031041 / 1000000000) := by
  have h := checkLog_sound (w := (70694087403 / 4070694087403)) (n := 12)
    (lo := (17368339 / 500000000)) (hi := (34736679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2070694087403 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2070694087403 / 2000000000000) = 1/(500000000000 / 2070694087403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13082 : Bounds (710515519 / 500000000) (1421031041 / 1000000000) (Real.log (2070694087403 / 500000000000)) := by
  have h := reflection_log_13082_neg
  have he : Real.log (2070694087403 / 500000000000) = -Real.log (500000000000 / 2070694087403) := by
    rw [show ((2070694087403 / 500000000000) : ℝ) = ((500000000000 / 2070694087403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13083_neg : (715316739 / 500000000) ≤ -Real.log (50000000000 / 209067357513) ∧
    -Real.log (50000000000 / 209067357513) ≤ (1430633481 / 1000000000) := by
  have h := checkLog_sound (w := (9067357513 / 409067357513)) (n := 12)
    (lo := (22169559 / 500000000)) (hi := (44339119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209067357513 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(209067357513 / 200000000000) = 1/(50000000000 / 209067357513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13083 : Bounds (715316739 / 500000000) (1430633481 / 1000000000) (Real.log (209067357513 / 50000000000)) := by
  have h := reflection_log_13083_neg
  have he : Real.log (209067357513 / 50000000000) = -Real.log (50000000000 / 209067357513) := by
    rw [show ((209067357513 / 50000000000) : ℝ) = ((50000000000 / 209067357513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13084_neg : (24028629 / 50000000) ≤ -Real.log (1000 / 1617) ∧
    -Real.log (1000 / 1617) ≤ (480572581 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 2617)) (n := 12)
    (lo := (24028629 / 50000000)) (hi := (480572581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1617 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1617 / 1000) = 1/(1000 / 1617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13084 : Bounds (24028629 / 50000000) (480572581 / 1000000000) (Real.log (1617 / 1000)) := by
  have h := reflection_log_13084_neg
  have he : Real.log (1617 / 1000) = -Real.log (1000 / 1617) := by
    rw [show ((1617 / 1000) : ℝ) = ((1000 / 1617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13085_neg : (959720289 / 1000000000) ≤ -Real.log (383 / 1000) ∧
    -Real.log (383 / 1000) ≤ (959720291 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 883)) (n := 12)
    (lo := (266573109 / 1000000000)) (hi := (26657311 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 383) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 383) = 1/(383 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13085 : Bounds (-959720291 / 1000000000) (-959720289 / 1000000000) (Real.log (383 / 1000)) := by
  have h := reflection_log_13085_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13086_neg : (616809 / 1000000000) ≤ -Real.log (1000000 / 1000617) ∧
    -Real.log (1000000 / 1000617) ≤ (61681 / 100000000) := by
  have h := checkLog_sound (w := (617 / 2000617)) (n := 12)
    (lo := (616809 / 1000000000)) (hi := (61681 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000617 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000617 / 1000000) = 1/(1000000 / 1000617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13086 : Bounds (616809 / 1000000000) (61681 / 100000000) (Real.log (1000617 / 1000000)) := by
  have h := reflection_log_13086_neg
  have he : Real.log (1000617 / 1000000) = -Real.log (1000000 / 1000617) := by
    rw [show ((1000617 / 1000000) : ℝ) = ((1000000 / 1000617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13087_neg : (61719 / 100000000) ≤ -Real.log (999383 / 1000000) ∧
    -Real.log (999383 / 1000000) ≤ (617191 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 1999383)) (n := 12)
    (lo := (61719 / 100000000)) (hi := (617191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999383) = 1/(999383 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13087 : Bounds (-617191 / 1000000000) (-61719 / 100000000) (Real.log (999383 / 1000000)) := by
  have h := reflection_log_13087_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13088_neg : (285456347 / 1000000000) ≤ -Real.log (1000000 / 1330369) ∧
    -Real.log (1000000 / 1330369) ≤ (71364087 / 250000000) := by
  have h := checkLog_sound (w := (330369 / 2330369)) (n := 12)
    (lo := (285456347 / 1000000000)) (hi := (71364087 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1330369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1330369 / 1000000) = 1/(1000000 / 1330369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13088 : Bounds (285456347 / 1000000000) (71364087 / 250000000) (Real.log (1330369 / 1000000)) := by
  have h := reflection_log_13088_neg
  have he : Real.log (1330369 / 1000000) = -Real.log (1000000 / 1330369) := by
    rw [show ((1330369 / 1000000) : ℝ) = ((1000000 / 1330369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13089_neg : (25064279 / 62500000) ≤ -Real.log (669631 / 1000000) ∧
    -Real.log (669631 / 1000000) ≤ (80205693 / 200000000) := by
  have h := checkLog_sound (w := (330369 / 1669631)) (n := 12)
    (lo := (25064279 / 62500000)) (hi := (80205693 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 669631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 669631) = 1/(669631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13089 : Bounds (-80205693 / 200000000) (-25064279 / 62500000) (Real.log (669631 / 1000000)) := by
  have h := reflection_log_13089_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13090_neg : (143646623 / 500000000) ≤ -Real.log (200000 / 266563) ∧
    -Real.log (200000 / 266563) ≤ (287293247 / 1000000000) := by
  have h := checkLog_sound (w := (66563 / 466563)) (n := 12)
    (lo := (143646623 / 500000000)) (hi := (287293247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((266563 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(266563 / 200000) = 1/(200000 / 266563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13090 : Bounds (143646623 / 500000000) (287293247 / 1000000000) (Real.log (266563 / 200000)) := by
  have h := reflection_log_13090_neg
  have he : Real.log (266563 / 200000) = -Real.log (200000 / 266563) := by
    rw [show ((266563 / 200000) : ℝ) = ((200000 / 266563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13091_neg : (40468791 / 100000000) ≤ -Real.log (133437 / 200000) ∧
    -Real.log (133437 / 200000) ≤ (404687911 / 1000000000) := by
  have h := checkLog_sound (w := (66563 / 333437)) (n := 12)
    (lo := (40468791 / 100000000)) (hi := (404687911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 133437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 133437) = 1/(133437 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13091 : Bounds (-404687911 / 1000000000) (-40468791 / 100000000) (Real.log (133437 / 200000)) := by
  have h := reflection_log_13091_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13092_neg : (117394663 / 1000000000) ≤ -Real.log (35569367031 / 40000000000) ∧
    -Real.log (35569367031 / 40000000000) ≤ (14674333 / 125000000) := by
  have h := checkLog_sound (w := (4430632969 / 75569367031)) (n := 12)
    (lo := (117394663 / 1000000000)) (hi := (14674333 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 35569367031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 35569367031) = 1/(35569367031 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13092 : Bounds (-14674333 / 125000000) (-117394663 / 1000000000) (Real.log (35569367031 / 40000000000)) := by
  have h := reflection_log_13092_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13093_neg : (115572117 / 1000000000) ≤ -Real.log (890856323839 / 1000000000000) ∧
    -Real.log (890856323839 / 1000000000000) ≤ (57786059 / 500000000) := by
  have h := checkLog_sound (w := (109143676161 / 1890856323839)) (n := 12)
    (lo := (115572117 / 1000000000)) (hi := (57786059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 890856323839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 890856323839) = 1/(890856323839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13093 : Bounds (-57786059 / 500000000) (-115572117 / 1000000000) (Real.log (890856323839 / 1000000000000)) := by
  have h := reflection_log_13093_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13094_neg : (686484811 / 1000000000) ≤ -Real.log (500000000000 / 993359775757) ∧
    -Real.log (500000000000 / 993359775757) ≤ (171621203 / 250000000) := by
  have h := checkLog_sound (w := (493359775757 / 1493359775757)) (n := 12)
    (lo := (686484811 / 1000000000)) (hi := (171621203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((993359775757 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(993359775757 / 500000000000) = 1/(500000000000 / 993359775757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13094 : Bounds (686484811 / 1000000000) (171621203 / 250000000) (Real.log (993359775757 / 500000000000)) := by
  have h := reflection_log_13094_neg
  have he : Real.log (993359775757 / 500000000000) = -Real.log (500000000000 / 993359775757) := by
    rw [show ((993359775757 / 500000000000) : ℝ) = ((500000000000 / 993359775757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13095_neg : (691981157 / 1000000000) ≤ -Real.log (100000000000 / 199766931211) ∧
    -Real.log (100000000000 / 199766931211) ≤ (345990579 / 500000000) := by
  have h := checkLog_sound (w := (99766931211 / 299766931211)) (n := 12)
    (lo := (691981157 / 1000000000)) (hi := (345990579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199766931211 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199766931211 / 100000000000) = 1/(100000000000 / 199766931211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13095 : Bounds (691981157 / 1000000000) (345990579 / 500000000) (Real.log (199766931211 / 100000000000)) := by
  have h := reflection_log_13095_neg
  have he : Real.log (199766931211 / 100000000000) = -Real.log (100000000000 / 199766931211) := by
    rw [show ((199766931211 / 100000000000) : ℝ) = ((100000000000 / 199766931211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13096_neg : (715316739 / 500000000) ≤ -Real.log (500000000000 / 2090673575129) ∧
    -Real.log (500000000000 / 2090673575129) ≤ (1430633481 / 1000000000) := by
  have h := checkLog_sound (w := (90673575129 / 4090673575129)) (n := 12)
    (lo := (22169559 / 500000000)) (hi := (44339119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2090673575129 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2090673575129 / 2000000000000) = 1/(500000000000 / 2090673575129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13096 : Bounds (715316739 / 500000000) (1430633481 / 1000000000) (Real.log (2090673575129 / 500000000000)) := by
  have h := reflection_log_13096_neg
  have he : Real.log (2090673575129 / 500000000000) = -Real.log (500000000000 / 2090673575129) := by
    rw [show ((2090673575129 / 500000000000) : ℝ) = ((500000000000 / 2090673575129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13097_neg : (1440292869 / 1000000000) ≤ -Real.log (250000000000 / 1055483028721) ∧
    -Real.log (250000000000 / 1055483028721) ≤ (180036609 / 125000000) := by
  have h := checkLog_sound (w := (55483028721 / 2055483028721)) (n := 12)
    (lo := (53998509 / 1000000000)) (hi := (5399851 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1055483028721 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1055483028721 / 1000000000000) = 1/(250000000000 / 1055483028721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13097 : Bounds (1440292869 / 1000000000) (180036609 / 125000000) (Real.log (1055483028721 / 250000000000)) := by
  have h := reflection_log_13097_neg
  have he : Real.log (1055483028721 / 250000000000) = -Real.log (250000000000 / 1055483028721) := by
    rw [show ((1055483028721 / 250000000000) : ℝ) = ((250000000000 / 1055483028721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13098_neg : (482426149 / 1000000000) ≤ -Real.log (50 / 81) ∧
    -Real.log (50 / 81) ≤ (9648523 / 20000000) := by
  have h := checkLog_sound (w := (31 / 131)) (n := 12)
    (lo := (482426149 / 1000000000)) (hi := (9648523 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81 / 50) = 1/(50 / 81) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13098 : Bounds (482426149 / 1000000000) (9648523 / 20000000) (Real.log (81 / 50)) := by
  have h := reflection_log_13098_neg
  have he : Real.log (81 / 50) = -Real.log (50 / 81) := by
    rw [show ((81 / 50) : ℝ) = ((50 / 81) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13099_neg : (38703361 / 40000000) ≤ -Real.log (19 / 50) ∧
    -Real.log (19 / 50) ≤ (967584027 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 22)) (n := 12)
    (lo := (54887369 / 200000000)) (hi := (137218423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 19) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25 / 19) = 1/(19 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13099 : Bounds (-967584027 / 1000000000) (-38703361 / 40000000) (Real.log (19 / 50)) := by
  have h := reflection_log_13099_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13100_neg : (619807 / 1000000000) ≤ -Real.log (50000 / 50031) ∧
    -Real.log (50000 / 50031) ≤ (19369 / 31250000) := by
  have h := checkLog_sound (w := (31 / 100031)) (n := 12)
    (lo := (619807 / 1000000000)) (hi := (19369 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50031 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50031 / 50000) = 1/(50000 / 50031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13100 : Bounds (619807 / 1000000000) (19369 / 31250000) (Real.log (50031 / 50000)) := by
  have h := reflection_log_13100_neg
  have he : Real.log (50031 / 50000) = -Real.log (50000 / 50031) := by
    rw [show ((50031 / 50000) : ℝ) = ((50000 / 50031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13101_neg : (19381 / 31250000) ≤ -Real.log (49969 / 50000) ∧
    -Real.log (49969 / 50000) ≤ (620193 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 99969)) (n := 12)
    (lo := (19381 / 31250000)) (hi := (620193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49969) = 1/(49969 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13101 : Bounds (-620193 / 1000000000) (-19381 / 31250000) (Real.log (49969 / 50000)) := by
  have h := reflection_log_13101_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13102_neg : (35858749 / 125000000) ≤ -Real.log (1000000 / 1332251) ∧
    -Real.log (1000000 / 1332251) ≤ (286869993 / 1000000000) := by
  have h := checkLog_sound (w := (332251 / 2332251)) (n := 12)
    (lo := (35858749 / 125000000)) (hi := (286869993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1332251 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1332251 / 1000000) = 1/(1000000 / 1332251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13102 : Bounds (35858749 / 125000000) (286869993 / 1000000000) (Real.log (1332251 / 1000000)) := by
  have h := reflection_log_13102_neg
  have he : Real.log (1332251 / 1000000) = -Real.log (1000000 / 1332251) := by
    rw [show ((1332251 / 1000000) : ℝ) = ((1000000 / 1332251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13103_neg : (100960731 / 250000000) ≤ -Real.log (667749 / 1000000) ∧
    -Real.log (667749 / 1000000) ≤ (16153717 / 40000000) := by
  have h := checkLog_sound (w := (332251 / 1667749)) (n := 12)
    (lo := (100960731 / 250000000)) (hi := (16153717 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 667749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 667749) = 1/(667749 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13103 : Bounds (-16153717 / 40000000) (-100960731 / 250000000) (Real.log (667749 / 1000000)) := by
  have h := reflection_log_13103_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13104_neg : (57741759 / 200000000) ≤ -Real.log (1000000 / 1334703) ∧
    -Real.log (1000000 / 1334703) ≤ (72177199 / 250000000) := by
  have h := checkLog_sound (w := (334703 / 2334703)) (n := 12)
    (lo := (57741759 / 200000000)) (hi := (72177199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1334703 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1334703 / 1000000) = 1/(1000000 / 1334703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13104 : Bounds (57741759 / 200000000) (72177199 / 250000000) (Real.log (1334703 / 1000000)) := by
  have h := reflection_log_13104_neg
  have he : Real.log (1334703 / 1000000) = -Real.log (1000000 / 1334703) := by
    rw [show ((1334703 / 1000000) : ℝ) = ((1000000 / 1334703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13105_neg : (407521721 / 1000000000) ≤ -Real.log (665297 / 1000000) ∧
    -Real.log (665297 / 1000000) ≤ (203760861 / 500000000) := by
  have h := checkLog_sound (w := (334703 / 1665297)) (n := 12)
    (lo := (407521721 / 1000000000)) (hi := (203760861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 665297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 665297) = 1/(665297 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13105 : Bounds (-203760861 / 500000000) (-407521721 / 1000000000) (Real.log (665297 / 1000000)) := by
  have h := reflection_log_13105_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13106_neg : (59406463 / 500000000) ≤ -Real.log (887973901791 / 1000000000000) ∧
    -Real.log (887973901791 / 1000000000000) ≤ (118812927 / 1000000000) := by
  have h := checkLog_sound (w := (112026098209 / 1887973901791)) (n := 12)
    (lo := (59406463 / 500000000)) (hi := (118812927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 887973901791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 887973901791) = 1/(887973901791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13106 : Bounds (-118812927 / 1000000000) (-59406463 / 500000000) (Real.log (887973901791 / 1000000000000)) := by
  have h := reflection_log_13106_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13107_neg : (116972931 / 1000000000) ≤ -Real.log (889609272999 / 1000000000000) ∧
    -Real.log (889609272999 / 1000000000000) ≤ (29243233 / 250000000) := by
  have h := checkLog_sound (w := (110390727001 / 1889609272999)) (n := 12)
    (lo := (116972931 / 1000000000)) (hi := (29243233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 889609272999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 889609272999) = 1/(889609272999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13107 : Bounds (-29243233 / 250000000) (-116972931 / 1000000000) (Real.log (889609272999 / 1000000000000)) := by
  have h := reflection_log_13107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13108_neg : (690712917 / 1000000000) ≤ -Real.log (25000000000 / 49878434861) ∧
    -Real.log (25000000000 / 49878434861) ≤ (345356459 / 500000000) := by
  have h := checkLog_sound (w := (24878434861 / 74878434861)) (n := 12)
    (lo := (690712917 / 1000000000)) (hi := (345356459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49878434861 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49878434861 / 25000000000) = 1/(25000000000 / 49878434861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13108 : Bounds (690712917 / 1000000000) (345356459 / 500000000) (Real.log (49878434861 / 25000000000)) := by
  have h := reflection_log_13108_neg
  have he : Real.log (49878434861 / 25000000000) = -Real.log (25000000000 / 49878434861) := by
    rw [show ((49878434861 / 25000000000) : ℝ) = ((25000000000 / 49878434861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13109_neg : (174057629 / 250000000) ≤ -Real.log (500000000000 / 1003088094491) ∧
    -Real.log (500000000000 / 1003088094491) ≤ (348115259 / 500000000) := by
  have h := checkLog_sound (w := (3088094491 / 2003088094491)) (n := 12)
    (lo := (385417 / 125000000)) (hi := (3083337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1003088094491 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1003088094491 / 1000000000000) = 1/(500000000000 / 1003088094491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13109 : Bounds (174057629 / 250000000) (348115259 / 500000000) (Real.log (1003088094491 / 500000000000)) := by
  have h := reflection_log_13109_neg
  have he : Real.log (1003088094491 / 500000000000) = -Real.log (500000000000 / 1003088094491) := by
    rw [show ((1003088094491 / 500000000000) : ℝ) = ((500000000000 / 1003088094491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13110_neg : (1440292869 / 1000000000) ≤ -Real.log (500000000000 / 2110966057441) ∧
    -Real.log (500000000000 / 2110966057441) ≤ (180036609 / 125000000) := by
  have h := checkLog_sound (w := (110966057441 / 4110966057441)) (n := 12)
    (lo := (53998509 / 1000000000)) (hi := (5399851 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2110966057441 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2110966057441 / 2000000000000) = 1/(500000000000 / 2110966057441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13110 : Bounds (1440292869 / 1000000000) (180036609 / 125000000) (Real.log (2110966057441 / 500000000000)) := by
  have h := reflection_log_13110_neg
  have he : Real.log (2110966057441 / 500000000000) = -Real.log (500000000000 / 2110966057441) := by
    rw [show ((2110966057441 / 500000000000) : ℝ) = ((500000000000 / 2110966057441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13111_neg : (725005087 / 500000000) ≤ -Real.log (500000000000 / 2131578947369) ∧
    -Real.log (500000000000 / 2131578947369) ≤ (1450010177 / 1000000000) := by
  have h := checkLog_sound (w := (131578947369 / 4131578947369)) (n := 12)
    (lo := (31857907 / 500000000)) (hi := (12743163 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2131578947369 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2131578947369 / 2000000000000) = 1/(500000000000 / 2131578947369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13111 : Bounds (725005087 / 500000000) (1450010177 / 1000000000) (Real.log (2131578947369 / 500000000000)) := by
  have h := reflection_log_13111_neg
  have he : Real.log (2131578947369 / 500000000000) = -Real.log (500000000000 / 2131578947369) := by
    rw [show ((2131578947369 / 500000000000) : ℝ) = ((500000000000 / 2131578947369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13112_neg : (7566817 / 15625000) ≤ -Real.log (1000 / 1623) ∧
    -Real.log (1000 / 1623) ≤ (484276289 / 1000000000) := by
  have h := checkLog_sound (w := (623 / 2623)) (n := 12)
    (lo := (7566817 / 15625000)) (hi := (484276289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1623 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1623 / 1000) = 1/(1000 / 1623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13112 : Bounds (7566817 / 15625000) (484276289 / 1000000000) (Real.log (1623 / 1000)) := by
  have h := reflection_log_13112_neg
  have he : Real.log (1623 / 1000) = -Real.log (1000 / 1623) := by
    rw [show ((1623 / 1000) : ℝ) = ((1000 / 1623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13113_neg : (97551009 / 100000000) ≤ -Real.log (377 / 1000) ∧
    -Real.log (377 / 1000) ≤ (243877523 / 250000000) := by
  have h := checkLog_sound (w := (123 / 877)) (n := 12)
    (lo := (28236291 / 100000000)) (hi := (282362911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 377) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 377) = 1/(377 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13113 : Bounds (-243877523 / 250000000) (-97551009 / 100000000) (Real.log (377 / 1000)) := by
  have h := reflection_log_13113_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13114_neg : (311403 / 500000000) ≤ -Real.log (1000000 / 1000623) ∧
    -Real.log (1000000 / 1000623) ≤ (622807 / 1000000000) := by
  have h := checkLog_sound (w := (623 / 2000623)) (n := 12)
    (lo := (311403 / 500000000)) (hi := (622807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000623 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000623 / 1000000) = 1/(1000000 / 1000623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13114 : Bounds (311403 / 500000000) (622807 / 1000000000) (Real.log (1000623 / 1000000)) := by
  have h := reflection_log_13114_neg
  have he : Real.log (1000623 / 1000000) = -Real.log (1000000 / 1000623) := by
    rw [show ((1000623 / 1000000) : ℝ) = ((1000000 / 1000623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13115_neg : (311597 / 500000000) ≤ -Real.log (999377 / 1000000) ∧
    -Real.log (999377 / 1000000) ≤ (124639 / 200000000) := by
  have h := checkLog_sound (w := (623 / 1999377)) (n := 12)
    (lo := (311597 / 500000000)) (hi := (124639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999377) = 1/(999377 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13115 : Bounds (-124639 / 200000000) (-311597 / 500000000) (Real.log (999377 / 1000000)) := by
  have h := reflection_log_13115_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13116_neg : (1801779 / 6250000) ≤ -Real.log (1000000 / 1334137) ∧
    -Real.log (1000000 / 1334137) ≤ (288284641 / 1000000000) := by
  have h := checkLog_sound (w := (334137 / 2334137)) (n := 12)
    (lo := (1801779 / 6250000)) (hi := (288284641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1334137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1334137 / 1000000) = 1/(1000000 / 1334137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13116 : Bounds (1801779 / 6250000) (288284641 / 1000000000) (Real.log (1334137 / 1000000)) := by
  have h := reflection_log_13116_neg
  have he : Real.log (1334137 / 1000000) = -Real.log (1000000 / 1334137) := by
    rw [show ((1334137 / 1000000) : ℝ) = ((1000000 / 1334137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13117_neg : (81334267 / 200000000) ≤ -Real.log (665863 / 1000000) ∧
    -Real.log (665863 / 1000000) ≤ (50833917 / 125000000) := by
  have h := checkLog_sound (w := (334137 / 1665863)) (n := 12)
    (lo := (81334267 / 200000000)) (hi := (50833917 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 665863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 665863) = 1/(665863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13117 : Bounds (-50833917 / 125000000) (-81334267 / 200000000) (Real.log (665863 / 1000000)) := by
  have h := reflection_log_13117_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13118_neg : (290126083 / 1000000000) ≤ -Real.log (250000 / 334149) ∧
    -Real.log (250000 / 334149) ≤ (72531521 / 250000000) := by
  have h := checkLog_sound (w := (84149 / 584149)) (n := 12)
    (lo := (290126083 / 1000000000)) (hi := (72531521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334149 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(334149 / 250000) = 1/(250000 / 334149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13118 : Bounds (290126083 / 1000000000) (72531521 / 250000000) (Real.log (334149 / 250000)) := by
  have h := reflection_log_13118_neg
  have he : Real.log (334149 / 250000) = -Real.log (250000 / 334149) := by
    rw [show ((334149 / 250000) : ℝ) = ((250000 / 334149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13119_neg : (205185561 / 500000000) ≤ -Real.log (165851 / 250000) ∧
    -Real.log (165851 / 250000) ≤ (410371123 / 1000000000) := by
  have h := checkLog_sound (w := (84149 / 415851)) (n := 12)
    (lo := (205185561 / 500000000)) (hi := (410371123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 165851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 165851) = 1/(165851 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13119 : Bounds (-410371123 / 1000000000) (-205185561 / 500000000) (Real.log (165851 / 250000)) := by
  have h := reflection_log_13119_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
